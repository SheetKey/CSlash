{-# LANGUAGE DeriveFunctor #-}

module CSlash.Tc.Solver.Monad where

import Prelude hiding ((<>))

import CSlash.Driver.Env

-- import qualified CSlash.Tc.Utils.Instantiate as TcM
-- import CSlash.Core.InstEnv
-- import GHC.Tc.Instance.Family as FamInst
-- import GHC.Core.FamInstEnv

import qualified CSlash.Tc.Utils.Monad as TcM
import qualified CSlash.Tc.Utils.TcMType as TcM
-- import qualified GHC.Tc.Instance.Class as TcM( matchGlobalInst, ClsInstResult(..) )
-- import qualified GHC.Tc.Utils.Env as TcM
--   ( checkWellStaged, tcGetDefaultTys
--   , tcLookupClass, tcLookupId, tcLookupTyCon
--   , topIdLvl )
import CSlash.Tc.Zonk.Monad ( ZonkM )
import qualified CSlash.Tc.Zonk.TcType as TcM
import qualified CSlash.Tc.Zonk.Type as TcM

import CSlash.Driver.DynFlags

-- import GHC.Tc.Instance.FunDeps( FunDepEqn(..) )
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Solver.Types
import CSlash.Tc.Solver.InertSet
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Errors.Types
import CSlash.Tc.Types
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Utils.Unify

-- import GHC.Builtin.Names ( unsatisfiableClassNameKey )

import CSlash.Core.Type
import CSlash.Core.Type.Rep as Rep
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs
-- import GHC.Core.Coercion
-- import GHC.Core.Coercion.Axiom( TypeEqn )
import CSlash.Core.Predicate
import CSlash.Core.Reduction
-- import GHC.Core.Class
import CSlash.Core.TyCon

import CSlash.Types.Name hiding (varName)
import CSlash.Types.TyThing
import CSlash.Types.Name.Reader
import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Types.Unique.Supply
import CSlash.Types.Unique.Set( elementOfUniqSet )

import CSlash.Unit.Module ( HasModule, getModule, extractModule )
import qualified CSlash.Rename.Env as TcM

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Logger
import CSlash.Utils.Misc (HasDebugCallStack)

import CSlash.Data.Bag as Bag
-- import GHC.Data.Pair

import CSlash.Utils.Monad

import GHC.Exts (oneShot)
import Control.Monad
import Data.IORef
import Data.List ( mapAccumL )
import Data.Foldable
import qualified Data.Semigroup as S
import CSlash.Types.SrcLoc
import CSlash.Rename.Env

{- *********************************************************************
*                                                                      *
               SolverStage and StopOrContinue
*                                                                      *
********************************************************************* -}

data StopOrContinue a
  = StartAgain Ct
  | ContinueWith !a
  | Stop CtEvidence SDoc
  deriving (Functor)

instance Outputable a => Outputable (StopOrContinue a) where
  ppr (Stop ev s) = text "Stop" <> parens (s $$ text "ev:" <+> ppr ev)
  ppr (ContinueWith w) = text "ContinueWith" <+> ppr w
  ppr (StartAgain w) = text "StartAgain" <+> ppr w

newtype SolverStage a = Stage { runSolverStage :: TcS (StopOrContinue a) }
  deriving (Functor)

instance Applicative SolverStage where
  pure x = Stage (return (ContinueWith x))
  (<*>) = ap

instance Monad SolverStage where
  return = pure
  (Stage m) >>= k = Stage $ do
    soc <- m
    case soc of
      StartAgain x -> return $ StartAgain x
      Stop ev d -> return $ Stop ev d
      ContinueWith x -> runSolverStage (k x)

simpleStage :: TcS a -> SolverStage a
simpleStage thing = Stage $ do
  res <- thing
  continueWith res

startAgainWith :: Ct -> TcS (StopOrContinue a)
startAgainWith ct = return $ StartAgain ct

continueWith :: a -> TcS (StopOrContinue a)
continueWith ct = return (ContinueWith ct)

stopWith :: CtEvidence -> String -> TcS (StopOrContinue a)
stopWith ev s = return $ Stop ev (text s)

stopWithStage :: CtEvidence -> String -> SolverStage a
stopWithStage ev s = Stage $ stopWith ev s

{- *********************************************************************
*                                                                      *
                  Kicking out
*                                                                      *
********************************************************************* -}

kickOutRewritable :: KickOutSpec -> CtFlavor -> TcS ()
kickOutRewritable ko_spec new_f = do
  ics <- getInertCans
  let (kicked_out, ics') = kickOutRewritableLHS ko_spec new_f ics
      n_kicked = lengthBag kicked_out
  setInertCans ics'

  unless (isEmptyBag kicked_out) $ do
    emitWork kicked_out
    csTraceTcS $ hang (text "Kick out")
                      2 $ vcat [ text "n-kicked =" <+> int n_kicked
                               , text "kicked_out =" <+> ppr kicked_out
                               , text "Residual inerts =" <+> ppr ics' ]

kickOutAfterUnification :: [TcKiVar] -> TcS ()
kickOutAfterUnification vs
  | null vs
  = return ()
  | otherwise
  = do let v_set = mkVarSet vs
       kickOutRewritable (KOAfterUnify v_set) Given

       let min_v_lvl = foldr1 minTcLevel (map varLevel vs)
       ambient_lvl <- getTcLevel
       when (ambient_lvl `strictlyDeeperThan` min_v_lvl)
         $ setUnificationFlag min_v_lvl
       return ()

kickOutAfterFillingCoercionHole :: AnyKindCoercionHole -> TcS ()
kickOutAfterFillingCoercionHole hole = do
  ics <- getInertCans
  let (kicked_out, ics') = kick_out ics
      n_kicked = lengthBag kicked_out
  unless (n_kicked == 0) $ do
    updWorkListTcS (extendWorkListCts (fmap CIrredCan kicked_out))
    csTraceTcS $
      hang (text "Kick out, hole =" <+> ppr hole)
           2 (vcat [ text "n-kicked =" <+> int n_kicked
                   , text "kicked_out =" <+> ppr kicked_out
                   , text "Residual inerts =" <+> ppr ics' ])
  setInertCans ics'
  where
    kick_out :: InertCans -> (Bag IrredCt, InertCans)
    kick_out ics@(IC { inert_irreds = irreds })
      = (irreds_to_kick, ics { inert_irreds = irreds_to_keep })
      where
        (irreds_to_kick, irreds_to_keep) = partitionBag kick_ct irreds

    kick_ct :: IrredCt -> Bool
    kick_ct ct
      | IrredCt { ir_ev = ev, ir_reason = reason } <- ct
      , CtWanted { ctev_rewriters = RewriterSet rewriters } <- ev
      , NonCanonicalReason ctyeq <- reason
      , ctyeq `ctkerHasProblem` ctkeCoercionHole
      , hole `elementOfUniqSet` rewriters
      = True
      | otherwise
      = False

{- *********************************************************************
*                                                                      *
                  Other inert-set operations
*                                                                      *
********************************************************************* -}

updInertSet :: (InertSet -> InertSet) -> TcS ()
updInertSet upd_fn = do
  is_var <- getInertSetRef
  wrapTcS $ do
    curr_inert <- TcM.readTcRef is_var
    TcM.writeTcRef is_var (upd_fn curr_inert)

getInertCans :: TcS InertCans
getInertCans = do
  inerts <- getInertSet
  return $ inert_cans inerts

setInertCans :: InertCans -> TcS ()
setInertCans ics = updInertSet $ \inerts -> inerts { inert_cans = ics }

updInertCans :: (InertCans -> InertCans) -> TcS ()
updInertCans upd_fn = updInertSet $ \inerts -> inerts { inert_cans = upd_fn (inert_cans inerts) }

getInertKiCos :: TcS InertKiCos
getInertKiCos = do
  inert <- getInertCans
  return $ inert_kicos inert

getInnermostGivenKiCoLevel :: TcS TcLevel
getInnermostGivenKiCoLevel = do
  inert <- getInertCans
  return $ inert_given_kico_lvl inert

getUnsolvedInerts :: TcS (Bag Implication, Cts)
getUnsolvedInerts = do
  IC { inert_kicos = kv_kicos
     , inert_irreds = irreds } <- getInertCans

  let unsolved_kv_kicos = foldKiCos (add_if_unsolved CKiCoCan) kv_kicos emptyCts
      unsolved_irreds = foldr (add_if_unsolved CIrredCan) emptyCts irreds

  implics <- getWorkListImplics

  traceTcS "getUnsolvedInerts"
    $ vcat [ text "kv kicos =" <+> ppr unsolved_kv_kicos
           , text "irreds =" <+> ppr unsolved_irreds 
           , text "implics =" <+> ppr implics ]

  return ( implics
         , unsolved_kv_kicos `andCts`
           unsolved_irreds )
  where
    add_if_unsolved :: (a -> Ct) -> a -> Cts -> Cts
    add_if_unsolved mk_ct thing cts
      | isWantedCt ct = ct `consCts` cts
      | otherwise = cts
      where ct = mk_ct thing

getHasGivenKiCos :: TcLevel -> TcS (HasGivenKiCos, InertIrreds) 
getHasGivenKiCos tclvl = do
  inerts@(IC { inert_irreds = irreds
             , inert_given_kicos = given_kicos
             , inert_given_kico_lvl = kc_lvl })
    <- getInertCans

  let given_insols = filterBag insoluble_given_equality irreds

      has_gkco | kc_lvl == tclvl = MaybeGivenKiCos
               | given_kicos = LocalGivenKiCos
               | otherwise = NoGivenKiCos

  traceTcS "getHasGivenEqs"
    $ vcat [ text "given_kicos:" <+> ppr given_kicos
           , text "kc_lvl:" <+> ppr kc_lvl
           , text "ambient level:" <+> ppr tclvl
           , text "Inerts:" <+> ppr inerts
           , text "Insols:" <+> ppr given_insols ]

  return (has_gkco, given_insols)
  where
    insoluble_given_equality (IrredCt { ir_ev = ev, ir_reason = reason })
      = isInsolubleReason reason && isGiven ev

{- *********************************************************************
*                                                                      *
*              The TcS solver monad                                    *
*                                                                      *
********************************************************************* -}

data TcSEnv = TcSEnv
  { tcs_ki_co_binds :: KiCoBindsVar
  , tcs_unified :: IORef Int
  , tcs_unif_lvl :: IORef (Maybe TcLevel)
  , tcs_count :: IORef Int
  , tcs_inerts :: IORef InertSet
  , tcs_abort_on_insoluble :: Bool
  , tcs_worklist :: IORef WorkList
  }

newtype TcS a = TcS {unTcS :: TcSEnv -> TcM a }
  deriving Functor

instance MonadFix TcS where
  mfix k = TcS $ \env -> mfix (\x -> unTcS (k x) env)

mkTcS :: (TcSEnv -> TcM a) -> TcS a
mkTcS f = TcS (oneShot f)

instance Applicative TcS where
  pure x = mkTcS $ \_ -> return x
  (<*>) = ap

instance Monad TcS where
  m >>= k = mkTcS $ \ebs -> do
    unTcS m ebs >>= (\r -> unTcS (k r) ebs)

instance MonadIO TcS where
  liftIO act = TcS $ \_ -> liftIO act

instance MonadFail TcS where
  fail err = mkTcS $ \_ -> fail err

instance HasModule TcS where
  getModule = wrapTcS getModule

wrapTcS :: TcM a -> TcS a
wrapTcS action = mkTcS $ \_ -> action

wrapErrTcS :: TcM a -> TcS a
wrapErrTcS = wrapTcS

failTcS :: TcRnMessage -> TcS a
failTcS = wrapTcS . TcM.failWith

addErrTcS :: TcRnMessage -> TcS ()
addErrTcS = wrapTcS . TcM.addErr

tryEarlyAbortTcS :: TcS ()
tryEarlyAbortTcS = mkTcS $ \env -> when (tcs_abort_on_insoluble env) TcM.failM

traceTcS :: String -> SDoc -> TcS ()
traceTcS herald doc = wrapTcS (TcM.traceTc herald doc)
{-# INLINE traceTcS #-}

instance HasDynFlags TcS where
  getDynFlags = wrapTcS getDynFlags

getGlobalRdrEnvTcS :: TcS GlobalRdrEnv
getGlobalRdrEnvTcS = wrapTcS TcM.getGlobalRdrEnv

bumpStepCountTcS :: TcS ()
bumpStepCountTcS = mkTcS $ \env -> do
  let ref = tcs_count env
  n <- TcM.readTcRef ref
  TcM.writeTcRef ref (n+1)

csTraceTcS :: SDoc -> TcS ()
csTraceTcS doc = wrapTcS $ csTraceTcM (return doc)
{-# INLINE csTraceTcS #-}

traceFireTcS :: CtEvidence -> SDoc -> TcS ()
traceFireTcS ev doc = mkTcS $ \env -> csTraceTcM $ do
  n <- TcM.readTcRef (tcs_count env)
  tclvl <- TcM.getTcLevel
  return $ hang (text "Step" <+> int n
                 <> brackets (text "l:" <> ppr tclvl <> comma <>
                              text "d:" <> ppr (ctLocDepth (ctEvLoc ev)))
                 <+> doc <> colon)
                4 (ppr ev)
{-# INLINE traceFireTcS #-}

csTraceTcM :: TcM SDoc -> TcM ()
csTraceTcM mk_doc = do
  logger <- getLogger
  when (logHasDumpFlag logger Opt_D_dump_cs_trace
        || logHasDumpFlag logger Opt_D_dump_tc_trace)
    $ do msg <- mk_doc
         TcM.dumpTcRn False Opt_D_dump_cs_trace "" FormatText msg
{-# INLINE csTraceTcM #-}

runTcSKindCoercions :: TcS a -> TcM a
runTcSKindCoercions thing_inside = do
  binds_var <- TcM.newTcKiCoBinds
  runTcSWithKiCoBinds binds_var thing_inside

runTcSWithKiCoBinds :: KiCoBindsVar -> TcS a -> TcM a
runTcSWithKiCoBinds = runTcSWithKiCoBinds' True False

runTcSWithKiCoBinds' :: Bool -> Bool -> KiCoBindsVar -> TcS a -> TcM a
runTcSWithKiCoBinds' restore_cycles abort_on_insoluble co_binds_var tcs = do
  unified_var <- TcM.newTcRef 0
  step_count <- TcM.newTcRef 0
  inert_var <- TcM.newTcRef emptyInert
  wl_var <- TcM.newTcRef emptyWorkList
  unif_lvl_var <- TcM.newTcRef Nothing
  let env = TcSEnv { tcs_ki_co_binds = co_binds_var
                   , tcs_unified = unified_var
                   , tcs_unif_lvl = unif_lvl_var
                   , tcs_count = step_count
                   , tcs_inerts = inert_var
                   , tcs_abort_on_insoluble = abort_on_insoluble
                   , tcs_worklist = wl_var }

  res <- unTcS tcs env

  count <- TcM.readTcRef step_count
  when (count > 0) $
    csTraceTcM $ return (text "Constraint solver steps =" <+> int count)

  -- when restore_cycles $ do
  --   inert_set <- TcM.readTcRef inert_var
  --   restoreTyVarCycles inert_set

  return res

nestImplicTcS :: KiCoBindsVar -> TcLevel -> TcS a -> TcS a
nestImplicTcS ref inner_tclvl (TcS thing_inside)
  = TcS $ \TcSEnv { tcs_unified = unified_var
                  , tcs_inerts = old_inert_var
                  , tcs_count = count
                  , tcs_unif_lvl = unif_lvl
                  , tcs_abort_on_insoluble = abort_on_insoluble } -> do
  inerts <- TcM.readTcRef old_inert_var
  let nest_inert = inerts { {-inert_cycle_breakers = pushCycleBreakerVarStack
                                                     (inert_cycle_breakers inerts)
                          , -}inert_cans = (inert_cans inerts) { inert_given_kicos = False }}
  new_inert_var <- TcM.newTcRef nest_inert
  new_wl_var <- TcM.newTcRef emptyWorkList
  let nest_env = TcSEnv { tcs_count = count
                        , tcs_unif_lvl = unif_lvl
                        , tcs_ki_co_binds = ref
                        , tcs_unified = unified_var
                        , tcs_inerts = new_inert_var
                        , tcs_abort_on_insoluble = abort_on_insoluble
                        , tcs_worklist = new_wl_var }
  res <- TcM.setTcLevel inner_tclvl $ thing_inside nest_env

  out_inert_set <- TcM.readTcRef new_inert_var
  -- restoreTyVarCycles out_inert_set

  return res

nestTcS :: TcS a -> TcS a
nestTcS (TcS thing_inside) = TcS $ \env@(TcSEnv { tcs_inerts = inerts_var }) -> do
  inerts <- TcM.readTcRef inerts_var
  new_inert_var <- TcM.newTcRef inerts
  new_wl_var <- TcM.newTcRef emptyWorkList
  let nest_env = env { tcs_inerts = new_inert_var
                     , tcs_worklist = new_wl_var }
  res <- thing_inside nest_env

  new_inerts <- TcM.readTcRef new_inert_var
  let old_ic = inert_cans inerts
      new_ic = inert_cans new_inerts
      nxt_ic = old_ic

  TcM.writeTcRef inerts_var (inerts { inert_cans = nxt_ic })

  return res

getUnifiedRef :: TcS (IORef Int)
getUnifiedRef = TcS (return . tcs_unified)

getInertSetRef :: TcS (IORef InertSet)
getInertSetRef = TcS (return . tcs_inerts)

getInertSet :: TcS InertSet
getInertSet = getInertSetRef >>= readTcRef

getTcSWorkListRef :: TcS (IORef WorkList)
getTcSWorkListRef = TcS (return . tcs_worklist)

getWorkListImplics :: TcS (Bag Implication)
getWorkListImplics = do
  wl_var <- getTcSWorkListRef
  wl_curr <- readTcRef wl_var
  return $ wl_implics wl_curr

updWorkListTcS :: (WorkList -> WorkList) -> TcS ()
updWorkListTcS f = do
  wl_var <- getTcSWorkListRef
  updTcRef wl_var f

emitWork :: Cts -> TcS ()
emitWork cts
  | isEmptyBag cts
  = return ()
  | otherwise
  = do traceTcS "Emitting fresh work" (pprBag cts)
       updWorkListTcS (extendWorkListCts cts)

newTcRef :: a -> TcS (TcRef a)
newTcRef x = wrapTcS (TcM.newTcRef x)

readTcRef :: TcRef a -> TcS a
readTcRef ref = wrapTcS (TcM.readTcRef ref)

writeTcRef :: TcRef a -> a -> TcS ()
writeTcRef ref val = wrapTcS (TcM.writeTcRef ref val)

updTcRef :: TcRef a -> (a -> a) -> TcS ()
updTcRef ref upd_fn = wrapTcS (TcM.updTcRef ref upd_fn)

getTcKiCoBindsVar :: TcS KiCoBindsVar
getTcKiCoBindsVar = TcS (return . tcs_ki_co_binds)

getTcLevel :: TcS TcLevel
getTcLevel = wrapTcS TcM.getTcLevel

getTcKiCoKiCoVars :: KiCoBindsVar -> TcS (MkVarSet (KiCoVar AnyKiVar))
getTcKiCoKiCoVars co_binds_var = wrapTcS $ TcM.getTcKiCoKiCoVars co_binds_var

unifyKiVar :: TcKiVar -> AnyMonoKind -> TcS ()
unifyKiVar kv ki
  = assertPpr (isMetaVar kv) (ppr kv)
    $ TcS $ \env -> do TcM.traceTc "unifyKiVar" (ppr kv <+> text ":=" <+> ppr ki)
                       TcM.liftZonkM $ TcM.writeMetaKiVar kv ki
                       TcM.updTcRef (tcs_unified env) (+1)

reportUnifications :: TcS a -> TcS (Int, a)
reportUnifications (TcS thing_inside) = TcS $ \env -> do
  inner_unified <- TcM.newTcRef 0
  res <- thing_inside (env { tcs_unified = inner_unified })
  n_unifs <- TcM.readTcRef inner_unified
  TcM.updTcRef (tcs_unified env) (+ n_unifs)
  return (n_unifs, res)

getWorkList :: TcS WorkList
getWorkList = do
  wl_var <- getTcSWorkListRef
  wrapTcS (TcM.readTcRef wl_var)

selectNextWorkItem :: TcS (Maybe Ct)
selectNextWorkItem = do
  wl_var <- getTcSWorkListRef
  wl <- readTcRef wl_var
  case selectWorkItem wl of
    Nothing -> return Nothing
    Just (ct, new_wl) -> do writeTcRef wl_var new_wl
                            return (Just ct)

isFilledMetaKiVar_maybe :: TcKiVar -> TcS (Maybe AnyMonoKind)
isFilledMetaKiVar_maybe kv = wrapTcS (TcM.isFilledMetaKiVar_maybe kv)

{- *********************************************************************
*                                                                      *
*              The Unification Level Flag                              *
*                                                                      *
********************************************************************* -}

resetUnificationFlag :: TcS Bool
resetUnificationFlag = TcS $ \env -> do
  let ref = tcs_unif_lvl env
  ambient_lvl <- TcM.getTcLevel
  mb_lvl <- TcM.readTcRef ref
  TcM.traceTc "resetUnificationFlag"
    $ vcat [ text "ambient:" <+> ppr ambient_lvl
           , text "unif_lvl:" <+> ppr mb_lvl ]
  case mb_lvl of
    Nothing -> return False
    Just unif_lvl | ambient_lvl `strictlyDeeperThan` unif_lvl
                    -> return False
                  | otherwise
                    -> do TcM.writeTcRef ref Nothing
                          return True    

setUnificationFlag :: TcLevel -> TcS ()
setUnificationFlag lvl = TcS $ \env -> do
  let ref = tcs_unif_lvl env
  mb_lvl <- TcM.readTcRef ref
  case mb_lvl of
    Just unif_lvl | lvl `deeperThanOrSame` unif_lvl
                    -> return ()
    _ -> TcM.writeTcRef ref (Just lvl)

{- *********************************************************************
*                                                                      *
*                Instantiation etc.
*                                                                      *
********************************************************************* -}

-- Creating and setting evidence variables and CtFlavors
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

-- data MaybeNew = Fresh CtEvidence | Cached KiEvType

-- getKiEvType :: MaybeNew -> KiEvType
-- getKiEvType (Fresh ctev) = ctEvType ctev
-- getKiEvType (Cached ev) = ev

useVars :: (MkVarSet (KiCoVar AnyKiVar)) -> TcS ()
useVars co_vars = do
  co_binds_var <- getTcKiCoBindsVar
  let ref = kcbv_kcvs co_binds_var
  wrapTcS $ do
    kcvs <- TcM.readTcRef ref
    let kcvs' = kcvs `unionVarSet` co_vars
    TcM.writeTcRef ref kcvs'

setWantedKiCo :: AnyKindCoercionHole -> AnyKindCoercion -> TcS ()
setWantedKiCo hole co = do
  useVars (coVarsOfKiCo co)
  fillKiCoercionHole hole co

fillKiCoercionHole :: AnyKindCoercionHole -> AnyKindCoercion -> TcS ()
fillKiCoercionHole hole co = do
  wrapTcS $ TcM.fillKiCoercionHole hole co
  kickOutAfterFillingCoercionHole hole

setKiCoBindIfWanted :: CtEvidence -> AnyKindCoercion -> TcS ()
setKiCoBindIfWanted ev ty = case ev of
  CtWanted { ctev_dest = dest } -> setWantedKiCo dest ty
  _ -> return ()

newKiCoVar :: AnyPredKind -> TcS (KiCoVar AnyKiVar)
newKiCoVar pred = wrapTcS (TcM.newKiCoVar pred)

newGivenKiCoVar :: CtLoc -> AnyPredKind -> TcS CtEvidence
newGivenKiCoVar loc pred = do
  new_covar <- newKiCoVar pred
  return (CtGiven { ctev_pred = pred, ctev_covar = new_covar, ctev_loc = loc })

newWantedKiCo
  :: CtLoc -> RewriterSet
  -> KiPred -> AnyMonoKind -> AnyMonoKind
  -> TcS (CtEvidence, AnyKindCoercion)
newWantedKiCo loc rewriters kc ki1 ki2 = do
  hole <- wrapTcS $ TcM.newKiCoercionHole pki
  return ( CtWanted { ctev_pred = pki
                    , ctev_dest = hole
                    , ctev_loc = loc
                    , ctev_rewriters = rewriters }
         , mkKiHoleCo hole )
  where
    pki = mkKiCoPred kc ki1 ki2

newWanted :: CtLoc -> RewriterSet -> AnyPredKind -> TcS CtEvidence
newWanted loc rewriters pki
  | (kc, k1, k2) <- getPredKis pki
  = fst <$> newWantedKiCo loc rewriters kc k1 k2
  | otherwise
  = pprPanic "newWanted" (ppr pki)

checkReductionDepth :: CtLoc -> AnyMonoKind -> TcS ()
checkReductionDepth loc ki = do
  dflags <- getDynFlags
  when (subGoalDepthExceeded (reductionDepth dflags) (ctLocDepth loc))
    $ wrapErrTcS $ solverDepthError loc ki

solverDepthError :: CtLoc -> AnyMonoKind -> TcM a
solverDepthError loc ki = panic "solverDepthError"

{- *********************************************************************
*                                                                      *
              Unification
*                                                                      *
********************************************************************* -}

wrapUnifierTcS :: CtEvidence -> (UnifyEnv -> TcM a) -> TcS (a, Bag Ct, [TcKiVar])
wrapUnifierTcS ev do_unifications = do
  (res, cts, unified, rewriters) <- wrapUnifierX ev do_unifications

  unless (isEmptyBag cts)
    $ updWorkListTcS (extendWorkListKiCos rewriters cts)

  _ <- kickOutAfterUnification unified

  return (res, cts, unified)

wrapUnifierX :: CtEvidence -> (UnifyEnv -> TcM a) -> TcS (a, Bag Ct, [TcKiVar], RewriterSet)
wrapUnifierX ev do_unifications = do
  unif_count_ref <- getUnifiedRef
  wrapTcS $ do
    defer_ref <- TcM.newTcRef emptyBag
    unified_ref <- TcM.newTcRef []
    rewriters <- TcM.zonkRewriterSet (ctEvRewriters ev)
    let env = UE { u_loc = ctEvLoc ev
                 , u_rewriters = rewriters
                 , u_defer = defer_ref
                 , u_unified = Just unified_ref }

    res <- do_unifications env
    
    cts <- TcM.readTcRef defer_ref
    unified <- TcM.readTcRef unified_ref

    unless (null unified)
      $ TcM.updTcRef unif_count_ref (+ (length unified))

    return (res, cts, unified, rewriters)

-- restoreTyVarCycles :: InertSet -> TcM ()
-- restoreTyVarCycles is = TcM.liftZonkM $
--   forAllCycleBreakerBindings_ (inert_cycle_breakers is) TcM.writeMetaTyVar

{- *********************************************************************
*                                                                      *
              Breaking type variable cycles
*                                                                      *
********************************************************************* -}

checkTouchableKiVarEq
  :: CtEvidence
  -> TcKiVar
  -> AnyMonoKind
  -> TcS (PuResult () Reduction)
checkTouchableKiVarEq ev lhs_kv rhs
  | simpleUnifyCheckKind lhs_kv rhs
  = do traceTcS "checkTouchableKiVarEq: simple-check wins" (ppr lhs_kv $$ ppr rhs)
       return $ pure $ mkReflRednKi rhs
  | otherwise
  = do traceTcS "checkTouchableKiVarEq {" (ppr lhs_kv $$ ppr rhs)
       check_result <- wrapTcS $ check_rhs rhs
       traceTcS "checkTouchableKiVarEq }" (ppr lhs_kv $$ ppr check_result)
       case check_result of
         PuFail reason -> return $ PuFail reason
         PuOK _ redn -> return $ pure redn
  where
    (lhs_kv_info, lhs_kv_lvl) = case tcVarDetails lhs_kv of
      MetaVar { mv_info = info, mv_tclvl = lvl } -> (info, lvl)
      _ -> pprPanic "checkTouchableKiVarEq" (ppr lhs_kv)

    check_rhs rhs = checkKiEqRhs flags rhs

    flags = KEF { kef_foralls = False
                , kef_unifying = Unifying lhs_kv_info lhs_kv_lvl LC_Promote
                , kef_lhs = KiVarLHS (toAnyKiVar lhs_kv)
                , kef_occurs = ctkeInsolubleOccurs }

checkKindEq :: CtEvidence -> CanKiCoLHS -> AnyMonoKind -> TcS (PuResult () Reduction)
checkKindEq ev lhs rhs
  | isGiven ev
  = do traceTcS "checkKindEq {" (vcat [ text "lhs:" <+> ppr lhs
                                      , text "rhs:" <+> ppr rhs ])
       check_result <- wrapTcS (checkKiEqRhs given_flags rhs)
       traceTcS "checkKindEq }" (ppr check_result)
       case check_result of
         PuFail reason -> return $ PuFail reason
         PuOK _ redn -> do return $ pure redn
  | otherwise
  = do check_result <- wrapTcS (checkKiEqRhs wanted_flags rhs)
       case check_result of
         PuFail reason -> return $ PuFail reason
         PuOK _ redn -> return $ pure redn
  where
    given_flags = KEF { kef_lhs = lhs
                      , kef_foralls = False
                      , kef_unifying = NotUnifying
                      , kef_occurs = ctkeInsolubleOccurs }

    wanted_flags = KEF { kef_lhs = lhs
                       , kef_foralls = False
                       , kef_unifying = NotUnifying
                       , kef_occurs = ctkeInsolubleOccurs }

