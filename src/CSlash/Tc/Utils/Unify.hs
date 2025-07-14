{-# LANGUAGE RecordWildCards #-}

module CSlash.Tc.Utils.Unify where

import Prelude hiding ((<>))

import CSlash.Cs

-- import GHC.Tc.Utils.Concrete ( hasFixedRuntimeRep, hasFixedRuntimeRep_syntactic )
import CSlash.Tc.Utils.Env
-- import GHC.Tc.Utils.Instantiate
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.BasicTypes
import CSlash.Tc.Zonk.TcType

import CSlash.Core.Type
import CSlash.Core.Type.Rep
-- import GHC.Core.TyCo.FVs( isInjectiveInType )
-- import CSlash.Core.Type.Ppr( debugPprType {- pprTyVar -} )
import CSlash.Core.TyCon
-- import GHC.Core.Coercion
import CSlash.Core.Kind
import CSlash.Core.Kind.Compare (tcEqKind, tcEqMonoKind)
import CSlash.Core.Reduction

import CSlash.Builtin.Types
import CSlash.Types.Name
-- import CSlash.Types.Id( idType )
import CSlash.Types.Var as Var
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.Basic
import CSlash.Types.Unique.Set (nonDetEltsUniqSet)

import CSlash.Utils.Error
import CSlash.Utils.Misc
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Trace

import CSlash.Driver.DynFlags
import CSlash.Data.Bag
import CSlash.Data.FastString( fsLit )

import Control.Monad
import Data.Monoid as DM ( Any(..) )
import qualified Data.Semigroup as S ( (<>) )

{- *********************************************************************
*                                                                      *
          Skolemization and matchExpectedFunTys
*                                                                      *
********************************************************************* -}

tcSkolemizeGeneral
  :: UserTypeCtxt
  -> AnyType -> AnyType
  -> ([(Name, AnyKiVar)] -> [(Name, AnyTyVar AnyKiVar)] -> AnyType -> TcM result)
  -> TcM (CsWrapper, result)
tcSkolemizeGeneral = panic "tcSkolemizeGeneral"

tcSkolemizeCompleteSig
  :: TcCompleteSig
  -> ([ExpPatType] -> AnyRhoType -> TcM result)
  -> TcM (CsWrapper, result)
tcSkolemizeCompleteSig (CSig { sig_bndr = poly_id, sig_ctxt = ctxt, sig_loc = loc })
                       thing_inside
  = do
  cur_loc <- getSrcSpanM
  let poly_ty = varType poly_id
  setSrcSpan loc $
    tcSkolemizeGeneral ctxt poly_ty poly_ty $ panic "tcSkolemizeCompleteSig"

checkKiConstraints :: SkolemInfoAnon -> [KiCoVar AnyKiVar] -> TcM result -> TcM result
checkKiConstraints skol_info given thing_inside = do
  implication_needed <- implicationNeeded skol_info given
  
  if implication_needed
    then do (tclvl, wanted, result) <- pushLevelAndCaptureConstraints thing_inside
            implics <- buildImplicationFor tclvl skol_info given wanted
            emitImplications implics
            return result
    else thing_inside

emitResidualKvConstraint :: SkolemInfo -> [TcKiVar] -> TcLevel -> WantedConstraints -> TcM ()
emitResidualKvConstraint skol_info skol_kvs tclvl wanted
  | not (isEmptyWC wanted)
    || checkTelescopeSkol skol_info_anon
  = do implic <- buildKvImplication skol_info_anon skol_kvs tclvl wanted
       emitImplication implic
  | otherwise
  = return ()
  where
    skol_info_anon = getSkolemInfo skol_info

buildKvImplication
  :: SkolemInfoAnon
  -> [TcKiVar]
  -> TcLevel
  -> WantedConstraints
  -> TcM Implication
buildKvImplication skol_info skol_kvs tclvl wanted
  = assertPpr (all (isSkolemVar <||> isTcVarVar) skol_kvs) (ppr skol_kvs) $ do
  ki_co_binds <- newTcKiCoBinds
  implic <- newImplication
  let implic' = implic { ic_tclvl = tclvl
                       , ic_skols = skol_kvs
                       , ic_given_kicos = NoGivenKiCos
                       , ic_wanted = wanted
                       , ic_binds = ki_co_binds
                       , ic_info = skol_info }
  checkImplicationInvariants implic'
  return implic'

emitResidualTvConstraint
  :: SkolemInfo
  -> [TcTyVar AnyKiVar]
  -> TcLevel
  -> WantedConstraints
  -> TcM ()
emitResidualTvConstraint skol_info skol_tvs tclvl wanted
  | not (isEmptyWC wanted)
    || checkTelescopeSkol skol_info_anon
  = do implic <- buildTvImplication skol_info_anon skol_tvs tclvl wanted
       emitImplication implic
  | otherwise
  = return ()
  where
    skol_info_anon = getSkolemInfo skol_info

buildTvImplication
  :: SkolemInfoAnon
  -> [TcTyVar AnyKiVar]
  -> TcLevel
  -> WantedConstraints
  -> TcM Implication
buildTvImplication skol_info skol_vs tclvl wanted
  = assertPpr (all (isSkolemVar <||> isTcVarVar) skol_vs) (ppr skol_vs) $ do
      traceTc "buildTvImplication ******************************"
        $ vcat [ ppr skol_vs, ppr skol_info, ppr wanted ]
      co_binds <- newTcKiCoBinds
      implic <- newImplication
      let implic' = implic { ic_tclvl = tclvl
                           , ic_skols = [] -- skol_vs
                           , ic_given_kicos = NoGivenKiCos
                           , ic_wanted = wanted
                           , ic_binds = co_binds
                           , ic_info = skol_info }
      checkImplicationInvariants implic'
      return implic'

implicationNeeded :: SkolemInfoAnon -> [KiCoVar kv] -> TcM Bool
implicationNeeded skol_info given
  | null given
  , not (alwaysBuildImplication skol_info)
  = do tc_lvl <- getTcLevel
       if not (isTopTcLevel tc_lvl)
         then return False
         else do dflags <- getDynFlags
                 return $ gopt Opt_DeferTypeErrors dflags
                       || gopt Opt_DeferTypedHoles dflags
                       || gopt Opt_DeferOutOfScopeVariables dflags
  | otherwise
  = return True

alwaysBuildImplication :: SkolemInfoAnon -> Bool
alwaysBuildImplication _ = False

buildImplicationFor
  :: TcLevel
  -> SkolemInfoAnon
  -> [KiCoVar AnyKiVar]
  -> WantedConstraints
  -> TcM (Bag Implication)
buildImplicationFor tclvl skol_info given wanted
  | isEmptyWC wanted && null given
  = return emptyBag
  | otherwise
  = do co_binds_var <- newTcKiCoBinds
       implic <- newImplication
       let implic' = implic { ic_tclvl = tclvl
                            , ic_skols = []
                            , ic_given = given
                            , ic_wanted = wanted
                            , ic_binds = co_binds_var
                            , ic_info = skol_info }
       checkImplicationInvariants implic'
       return (unitBag implic')

{- *********************************************************************
*                                                                      *
                Unification
*                                                                      *
********************************************************************* -}

unifyKind :: Maybe KindedThing -> KiPred -> AnyMonoKind -> AnyMonoKind -> TcM AnyKindCoercion
unifyKind thing kc ki1 ki2 = unifyKindAndEmit origin kc ki1 ki2
  where
    origin = KindCoOrigin { kco_actual = ki1
                          , kco_expected = ki2
                          , kco_pred = kc
                          , kco_thing = thing
                          , kco_visible = True }

unifyKindAndEmit :: CtOrigin -> KiPred -> AnyMonoKind -> AnyMonoKind -> TcM AnyKindCoercion
unifyKindAndEmit orig kc ki1 ki2 = do
  ref <- newTcRef emptyBag
  loc <- getCtLocM orig (Just KindLevel)
  let env = UE { u_loc = loc
               , u_rewriters = emptyRewriterSet
               , u_defer = ref
               , u_unified = Nothing }
  co <- uKind env kc ki1 ki2
  cts <- readTcRef ref
  unless (null cts) (emitSimples cts)
  return co

{- *********************************************************************
*                                                                      *
                uType and uKind
*                                                                      *
********************************************************************* -}

data UnifyEnv = UE
  { u_loc :: CtLoc
  , u_rewriters :: RewriterSet
  , u_defer :: TcRef Cts
  , u_unified :: Maybe (TcRef [TcKiVar])
  }

updUEnvLoc :: UnifyEnv -> (CtLoc -> CtLoc) -> UnifyEnv
updUEnvLoc uenv@(UE { u_loc = loc }) upd = uenv { u_loc = upd loc }

uKind_defer :: UnifyEnv -> KiPred -> AnyMonoKind -> AnyMonoKind -> TcM AnyKindCoercion
uKind_defer (UE { u_loc = loc, u_defer = ref, u_rewriters = rewriters }) kc ki1 ki2 = do
  let pred_ki = mkKiCoPred kc ki1 ki2
  hole <- newKiCoercionHole pred_ki
  let ct = mkNonCanonical
           $ CtWanted { ctev_pred = pred_ki
                      , ctev_dest = hole
                      , ctev_loc = loc
                      , ctev_rewriters = rewriters }
      co = HoleCo hole
  updTcRef ref (`snocBag` ct)
  whenDOptM Opt_D_dump_tc_trace $ do
    ctxt <- getErrCtxt
    doc <- mkErrInfo emptyTidyEnv ctxt
    traceTc "uKind_defer"
      $ vcat [ ppr kc, debugPprMonoKind ki1, debugPprMonoKind ki2, doc ]
    traceTc "uKind_defer2" (ppr co)

  return co

uKind :: UnifyEnv -> KiPred -> AnyMonoKind -> AnyMonoKind -> TcM AnyKindCoercion
uKind env kc orig_ki1 orig_ki2 = do
  tclvl <- getTcLevel
  traceTc "u_kis"
    $ vcat [ text "tclvl" <+> ppr tclvl
           , sep [ ppr orig_ki1, char '`' <> ppr kc <> char '`', ppr orig_ki2 ] ]
  co <- go orig_ki1 orig_ki2
  if isReflKiCo co
    then traceTc "u_kis yields no coercion" empty
    else traceTc "u_kis yields coercion:" (ppr co)
  return co
  where   
    go :: AnyMonoKind -> AnyMonoKind -> TcM AnyKindCoercion

    go (KiVarKi kv1) ki2 = do
      lookup_res <- handleAnyKv (const $ return Nothing) isFilledMetaKiVar_maybe kv1
      case lookup_res of
        Just ki1 -> do traceTc "found filled kivar" (ppr kv1 <+> text ":->" <+> ppr ki1)
                       uKind env kc ki1 orig_ki2
        Nothing -> uUnfilledKiVar env NotSwapped kc kv1 ki2

    go ki1 (KiVarKi kv2) = do
      lookup_res <- handleAnyKv (const $ return Nothing) isFilledMetaKiVar_maybe kv2
      case lookup_res of
        Just ki2 -> do traceTc "found filled kivar" (ppr kv2 <+> text ":->" <+> ppr ki2)
                       uKind env kc orig_ki1 ki2
        Nothing -> uUnfilledKiVar env IsSwapped kc kv2 ki1

    go ki1@(BIKi kc1) (BIKi kc2)
      | kc1 == kc2
      , EQKi <- kc
      = return $ mkReflKiCo ki1
      | kc1 == kc2
      , LTEQKi <- kc
      = return $ LiftEq $ mkReflKiCo ki1
      | kc1 < kc2
      , LTKi <- kc
      = case (kc1, kc2) of
          (UKd, AKd) -> return BI_U_A
          (AKd, LKd) -> return BI_A_L
          (UKd, LKd) -> return $ TransCo BI_U_A BI_A_L
          _ -> panic "unreachable"
      | kc1 < kc2
      , LTEQKi <- kc
      = case (kc1, kc2) of
          (UKd, AKd) -> return $ LiftLT BI_U_A
          (AKd, LKd) -> return $ LiftLT BI_A_L
          (UKd, LKd) -> return $ LiftLT $ TransCo BI_U_A BI_A_L
          _ -> panic "unreachable"

    go k1@(KiPredApp p1 ka1 kb1) k2@(KiPredApp p2 ka2 kb2) 
      | p1 == p2
      , EQKi <- kc -- maybe this should be an assert
      = do traceTc "go-kipred" (ppr k1 $$ ppr k2)
           coa <- u_kc_arg ka1 ka2 
           cob <- u_kc_arg kb1 kb2
           massertPpr (isReflKiCo coa && isReflKiCo cob)
             $ vcat [ text "uKind/go_kipred has non-reflexive argument coercion"
                    , ppr coa, ppr cob ]
           return $ mkReflKiCo k1

    go (FunKi FKF_K_K arg1 res1) (FunKi FKF_K_K arg2 res2) = do
      massertPpr (kc == EQKi)
        $ vcat [ text "uKind/go-funki has non-EQKi relation"
               , ppr kc, ppr orig_ki1, ppr orig_ki2 ]
      co_l <- uKind env kc arg1 arg2
      co_r <- uKind env kc res1 res2
      return $ mkFunKiCo FKF_K_K co_l co_r 

    go ki1 ki2 = defer kc ki1 ki2

    ------------------
    defer kc ki1 ki2
      | ki1 `tcEqMonoKind` ki2
      , EQKi <- kc
      = return $ mkReflKiCo ki1
      | ki1 `tcEqMonoKind` ki2
      , LTEQKi <- kc
      = return $ LiftEq $ mkReflKiCo ki1
      | otherwise = uKind_defer env kc orig_ki1 orig_ki2

    ------------------
    u_kc_arg ki1 ki2 = do
      traceTc "u_tc_arg" (ppr ki1 $$ ppr ki2)
      uKind env_arg kc ki1 ki2
      where
        env_arg = env { u_loc = adjustCtLoc False True (u_loc env) }

{- *********************************************************************
*                                                                      *
                 uUnfilledVar and friends
*                                                                      *
********************************************************************* -}

uUnfilledKiVar
  :: UnifyEnv -> SwapFlag -> KiPred -> AnyKiVar -> AnyMonoKind -> TcM AnyKindCoercion
uUnfilledKiVar env swapped kc kv1 ki2 = do
  ki2 <- liftZonkM $ zonkTcMonoKind ki2
  uUnfilledKiVar1 env swapped kc kv1 ki2

uUnfilledKiVar1
  :: UnifyEnv -> SwapFlag -> KiPred -> AnyKiVar -> AnyMonoKind -> TcM AnyKindCoercion
uUnfilledKiVar1 env swapped kc kv1 ki2
  | Just kv2 <- getKiVar_maybe ki2
  = go kv2
  | otherwise
  = uUnfilledKiVar2 env swapped kc kv1 ki2
  where
    go kv2
      | kv1 == kv2
      , EQKi <- kc
      = return $ mkReflKiCo (mkKiVarKi kv1)
      | kv1 == kv2
      , LTEQKi <- kc
      = return $ LiftEq $ mkReflKiCo (mkKiVarKi kv1)
      | swapOverKiVars False kv1 kv2
      = uUnfilledKiVar2 env (flipSwap swapped) kc kv2 (mkKiVarKi kv1)
      | otherwise
      = uUnfilledKiVar2 env swapped kc kv1 ki2

uUnfilledKiVar2
  :: UnifyEnv -> SwapFlag -> KiPred -> AnyKiVar -> AnyMonoKind -> TcM AnyKindCoercion
uUnfilledKiVar2 env swapped kc kv1 ki2 = do
  cur_lvl <- getTcLevel
  case toTcKiVar_maybe kv1 of
    Just tckv1
      | touchabilityAndShapeTestKind cur_lvl tckv1 ki2
      , simpleUnifyCheckKind tckv1 ki2
      , kc == EQKi
        -> do traceTc "uUnfilledKiVar2 ok" $ vcat [ ppr kc, ppr tckv1, ppr ki2 ]
              liftZonkM $ writeMetaKiVar tckv1 ki2
              case u_unified env of
                Nothing -> return ()
                Just uref -> updTcRef uref (tckv1 :)
              return $ case kc of
                         EQKi -> mkReflKiCo ki2
                         _ -> panic "unreachable"

    _ -> not_ok_so_defer
  where
    ki1 = mkKiVarKi kv1
    defer = unSwap swapped (uKind_defer env kc) ki1 ki2
    not_ok_so_defer = do
      traceTc "uUnfilledVar2 not ok" (ppr kv1 $$ ppr ki2)
      defer            

swapOverKiVars :: Bool -> AnyKiVar -> AnyKiVar -> Bool
swapOverKiVars is_given kv1 kv2
  | not is_given, pri1 == 0, pri2 > 0 = True
  | not is_given, pri2 == 0, pri1 > 0 = False

  | lvl1 `strictlyDeeperThan` lvl2 = False
  | lvl2 `strictlyDeeperThan` lvl1 = True

  | pri1 > pri2 = False
  | pri2 > pri1 = True

  | isSystemName kv2_name, not (isSystemName kv1_name) = True

  | otherwise = False
  where
    lvl1 = handleAnyKv (const topTcLevel) varLevel kv1
    lvl2 = handleAnyKv (const topTcLevel) varLevel kv2
    pri1 = lhsKiPriority kv1
    pri2 = lhsKiPriority kv2
    kv1_name = Var.varName kv1
    kv2_name = Var.varName kv2

lhsKiPriority :: AnyKiVar -> Int
lhsKiPriority =
  handleAnyKv (const 0) $ \ kv ->
  case tcVarDetails kv of
    SkolemVar {} -> 0
    MetaVar { mv_info = info } -> case info of
                                    VarVar -> 1
                                    TauVar -> 3

matchExpectedFunKind :: KindedThing -> Arity -> AnyMonoKind -> TcM AnyKindCoercion
matchExpectedFunKind cs_ty n k = go n k
  where
    go :: Arity -> AnyMonoKind -> TcM AnyKindCoercion
    go 0 k = return (mkReflKiCo k)
    go n k@(KiVarKi kvar)
      | Just kvar <- toTcKiVar_maybe kvar
      , isMetaVar kvar
      = do maybe_kind <- readMetaKiVar kvar
           case maybe_kind of
             Indirect fun_kind -> go n fun_kind
             Flexi -> defer n k
    go n (FunKi { fk_f = af, fk_arg = arg, fk_res = res })
      | isVisibleKiFunArg af
      = do co <- go (n-1) res
           return $ mkFunKiCo af (mkReflKiCo arg) co
    go n other = defer n other

    defer n k = do
      arg_kinds <- newMetaKindVars n
      res_kind <- newMetaKindVar
      let new_fun = asAnyKi $ mkVisFunKis arg_kinds res_kind
          origin = KindCoOrigin { kco_actual = k
                                , kco_expected = new_fun
                                , kco_pred = EQKi
                                , kco_thing = Just cs_ty
                                , kco_visible = True
                                }
      unifyKindAndEmit origin EQKi k new_fun

{- *********************************************************************
*                                                                      *
                 Checking alpha ~ ki
              for the on-the-fly unifier
*                                                                      *
********************************************************************* -}

simpleUnifyCheckKind  :: TcKiVar -> AnyMonoKind -> Bool
simpleUnifyCheckKind lhs_kv rhs = go_mono rhs
  where
    lhs_kv_lvl = varLevel lhs_kv

    go_mono (KiVarKi kv)
      | Just tckv <- toTcKiVar_maybe kv
      , lhs_kv == tckv = False
      | handleAnyKv (const topTcLevel) varLevel kv > lhs_kv_lvl = False
      | otherwise = True

    go_mono (FunKi { fk_f = af, fk_arg = a, fk_res = r })
      | af == FKF_C_K = False
      | otherwise = go_mono a && go_mono r

    go_mono (BIKi {}) = True

    go_mono (KiPredApp _ k1 k2) = go_mono k1 && go_mono k2

{- *********************************************************************
*                                                                      *
                 Equality invariant checking
*                                                                      *
********************************************************************* -}

data PuResult a b
  = PuFail CheckTyKiEqResult
  | PuOK (Bag a) b

instance Functor (PuResult a) where
  fmap _ (PuFail prob) = PuFail prob
  fmap f (PuOK cts x) = PuOK cts (f x)

instance Applicative (PuResult a) where
  pure x = PuOK emptyBag x
  PuFail p1 <*> PuFail p2 = PuFail (p1 S.<> p2)
  PuFail p1 <*> PuOK {} = PuFail p1
  PuOK {} <*> PuFail p2 = PuFail p2
  PuOK c1 f <*> PuOK c2 x = PuOK (c1 `unionBags` c2) (f x)

instance (Outputable a, Outputable b) => Outputable (PuResult a b) where
  ppr (PuFail prob) = text "PuFail" <+> (ppr prob)
  ppr (PuOK cts x) = text "PuOk" <> (braces
                     $ vcat [ text "redn:" <+> ppr x
                            , text "cts:" <+> ppr cts ])

okCheckReflKi :: AnyMonoKind -> TcM (PuResult a Reduction)
okCheckReflKi ki = return $ PuOK emptyBag $ mkReflRednKi ki

failCheckWith :: CheckTyKiEqResult -> TcM (PuResult a b)
failCheckWith p = return $ PuFail p

mapCheck :: (x -> TcM (PuResult a Reduction)) -> [x] -> TcM (PuResult a Reductions)
mapCheck f xs = do
  ress <- mapM f xs
  return (unzipRedns <$> sequenceA ress)

data KiEqFlags = KEF
  { kef_foralls :: Bool -- always false: we work only on monokinds (can prob remove)
  , kef_lhs :: CanKiCoLHS
  , kef_unifying :: AreUnifying
  , kef_occurs :: CheckTyKiEqProblem
  }

data AreUnifying
  = Unifying MetaInfo TcLevel LevelCheck
  | NotUnifying

data LevelCheck
  = LC_None
  | LC_Check
  | LC_Promote

instance Outputable KiEqFlags where
  ppr (KEF {..}) = text "KEF" <> (braces
                   $ vcat [ text "kef_lhs =" <+> ppr kef_lhs
                          , text "kef_unifying =" <+> ppr kef_unifying
                          , text "kef_occurs =" <+> ppr kef_occurs ])

instance Outputable AreUnifying where
  ppr NotUnifying = text "NotUnifying"
  ppr (Unifying mi lvl lc) = text "Unifying" <+>
                             (braces $ ppr mi <> comma <+> ppr lvl <> comma <+> ppr lc)

instance Outputable LevelCheck where
  ppr LC_None = text "LC_None"
  ppr LC_Check = text "LC_Check"
  ppr LC_Promote = text "LC_Promote"

checkKiEqRhs :: KiEqFlags -> AnyMonoKind -> TcM (PuResult () Reduction)
checkKiEqRhs flags ki = case ki of
  KiPredApp {} -> panic "checkKiEqRhs" --checkKiConApp flags ki kc kis
               -- maybe 'fail impredicative'??
  BIKi {} -> okCheckReflKi ki
  KiVarKi kv -> checkKiVar flags kv
  FunKi { fk_f = af, fk_arg = a, fk_res = r }
    | FKF_C_K <- af
    , not (kef_foralls flags)
    -> failCheckWith impredicativeProblem
    | otherwise
    -> do a_res <- checkKiEqRhs flags a
          r_res <- checkKiEqRhs flags r
          return $ mkFunKiRedn af <$> a_res <*> r_res

-- checkKiConApp
--   :: KiEqFlags -> AnyMonoKind -> KiCon -> [AnyMonoKind] -> TcM (PuResult () Reduction)
-- checkKiConApp flags kc_app kc kis
--   = recurseIntoKiConApp flags kc kis

-- recurseIntoKiConApp :: KiEqFlags -> KiCon -> [AnyMonoKind] -> TcM (PuResult () Reduction)
-- recurseIntoKiConApp flags kc kis = do
--   kis_res <- mapCheck (checkKiEqRhs flags) kis
--   return (mkKiConAppRedn kc <$> kis_res)

checkKiVar :: KiEqFlags -> AnyKiVar -> TcM (PuResult () Reduction)
checkKiVar (KEF { kef_lhs = lhs, kef_unifying = unifying, kef_occurs = occ_prob }) occ_kv
  = case lhs of
      KiVarLHS lhs_kv -> check_kv unifying lhs_kv
  where
    lvl_occ = handleAnyKv (const topTcLevel) varLevel occ_kv
    success = okCheckReflKi (mkKiVarKi occ_kv)

    check_kv :: AreUnifying -> AnyKiVar -> TcM (PuResult () Reduction)
    check_kv NotUnifying lhs_kv = simple_occurs_check lhs_kv
    check_kv (Unifying info lvl prom) lhs_kv = do
      mb_done <- handleAnyKv (const (return Nothing)) isFilledMetaKiVar_maybe occ_kv
      case mb_done of
        Just _ -> success
        Nothing -> check_unif info lvl prom lhs_kv

    check_unif :: MetaInfo -> TcLevel -> LevelCheck -> AnyKiVar -> TcM (PuResult a Reduction)
    check_unif lhs_kv_info lhs_kv_lvl prom lhs_kv
      -- | isConcreteInfo lhs_kv_info
      -- , not (isConcreteVar occ_kv)
      -- = case can_make_concrete occ_kv of
      --     Just tc_occ_kv -> promote lhs_kv lhs_kv_info lhs_kv_lvl tc_occ_kv
      --     Nothing -> failCheckWith (ctkeProblem ctkeConcrete)

      | lvl_occ `strictlyDeeperThan` lhs_kv_lvl
      = case prom of
          LC_None -> pprPanic "check_unif" (ppr lhs_kv $$ ppr occ_kv)
          LC_Check -> failCheckWith (ctkeProblem ctkeSkolemEscape)
          LC_Promote
            | Just tc_occ_kv <- toTcKiVar_maybe occ_kv
            , isMetaVar tc_occ_kv
              -> promote lhs_kv lhs_kv_info lhs_kv_lvl tc_occ_kv
            | otherwise
              -> failCheckWith (ctkeProblem ctkeSkolemEscape)

      | otherwise
      = simple_occurs_check lhs_kv

    simple_occurs_check lhs_kv
      | lhs_kv == occ_kv
      = failCheckWith (ctkeProblem occ_prob)
      | otherwise
      = success

    can_make_concrete occ_kv
      | Just tc_occ_kv <- toTcKiVar_maybe occ_kv
      , MetaVar { mv_info = TauVar } <- tcVarDetails tc_occ_kv
      = Just tc_occ_kv
      | otherwise
      = Nothing

    promote lhs_kv lhs_kv_info lhs_kv_lvl tc_occ_kv
      | MetaVar { mv_info = info_occ, mv_tclvl = lvl_occ } <- tcVarDetails tc_occ_kv
      = do let new_info -- | isConcreteInfo lhs_kv_info = lhs_kv_info
                        | otherwise = info_occ
               new_lvl = lhs_kv_lvl `minTcLevel` lvl_occ

           new_kv_ki <- promote_meta_kivar new_info new_lvl tc_occ_kv
           okCheckReflKi new_kv_ki
      | otherwise = pprPanic "promote" (ppr tc_occ_kv)

promote_meta_kivar :: MetaInfo -> TcLevel -> TcKiVar -> TcM AnyMonoKind
promote_meta_kivar info dest_lvl occ_kv = do
  mb_filled <- isFilledMetaKiVar_maybe occ_kv
  case mb_filled of
    Just ki -> return ki
    Nothing -> do new_kv <- toAnyKiVar <$> cloneMetaKiVarWithInfo info dest_lvl occ_kv
                  liftZonkM $ writeMetaKiVar occ_kv (mkKiVarKi new_kv)
                  traceTc "promoteKiVar" (ppr occ_kv <+> text "-->" <+> ppr new_kv)
                  return $ mkKiVarKi new_kv

touchabilityAndShapeTestKind :: TcLevel -> TcKiVar -> AnyMonoKind -> Bool
touchabilityAndShapeTestKind given_eq_lvl kv rhs
  | MetaVar { mv_info = info, mv_tclvl = kv_lvl } <- tcVarDetails kv
  , checkTopShapeKind info rhs
  = kv_lvl `deeperThanOrSame` given_eq_lvl
  | otherwise
  = False

checkTopShapeKind :: MetaInfo -> AnyMonoKind -> Bool
checkTopShapeKind info xi
  = case info of
      VarVar -> case getKiVar_maybe xi of
                  Nothing -> False
                  Just kv -> handleAnyKv (const True) helper kv
      _ -> True
  where
    helper kv = 
      case tcVarDetails kv of
        SkolemVar {} -> True
        MetaVar { mv_info = VarVar } -> True
        _ -> False
