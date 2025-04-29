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
-- import GHC.Tc.Types.Evidence
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
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

import CSlash.Driver.DynFlags
import CSlash.Data.Bag
import CSlash.Data.FastString( fsLit )

import Control.Monad
import Data.Monoid as DM ( Any(..) )
import qualified Data.Semigroup as S ( (<>) )

{- *********************************************************************
*                                                                      *
          Skolemisation and matchExpectedFunTys
*                                                                      *
********************************************************************* -}

emitResidualTvConstraint :: SkolemInfo -> [TcTyVar] -> TcLevel -> WantedConstraints -> TcM ()
emitResidualTvConstraint skol_info skol_tvs tclvl wanted
  | not (isEmptyWC wanted)
    || checkTelescopeSkol (getSkolemInfo skol_info)
  = do implic <- buildVImplication (getSkolemInfo skol_info) skol_tvs tclvl wanted
       emitImplication implic
  | otherwise
  = return ()

buildVImplication
  :: SkolemInfoAnon
  -> [TcVar]
  -> TcLevel
  -> WantedConstraints
  -> TcM Implication
buildVImplication skol_info skol_vs tclvl wanted
  = assertPpr (all (isSkolemTyVar
                    <||> isTyVarTyVar
                    <||> isSkolemKiVar
                    <||> isKiVarKiVar) skol_vs) (ppr skol_vs) $ do
      implic <- newImplication
      let implic' = implic { ic_tclvl = tclvl
                           , ic_skols = skol_vs
                           , ic_given_eqs = NoGivenEqs
                           , ic_wanted = wanted
                           , ic_info = skol_info }
      checkImplicationInvariants implic'
      return implic'

{- *********************************************************************
*                                                                      *
                Unification
*                                                                      *
********************************************************************* -}

unifyKindAndEmit :: CtOrigin -> TcMonoKind -> TcMonoKind -> TcM KindCoercion
unifyKindAndEmit orig ki1 ki2 = do
  ref <- newTcRef emptyBag
  loc <- getCtLocM orig (Just KindLevel)
  let env = UE { u_loc = loc
               , u_rewriters = emptyRewriterSet
               , u_defer = ref
               , u_unified = Nothing }
  co <- uKind env ki1 ki2
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
  , u_unified :: Maybe (TcRef [Var])
  }

updUEnvLoc :: UnifyEnv -> (CtLoc -> CtLoc) -> UnifyEnv
updUEnvLoc  uenv@(UE { u_loc = loc }) upd = uenv { u_loc = upd loc }

uKind_defer :: UnifyEnv -> TcMonoKind -> TcMonoKind -> TcM KindCoercion
uKind_defer (UE { u_loc = loc, u_defer = ref, u_rewriters = rewriters }) ki1 ki2 = do
  let pred_ki = mkKiEqPred ki1 ki2
  hole <- newKiCoercionHole pred_ki
  let ct = mkNonCanonical
           $ CtWanted { ctev_pred = pred_ki
                      , ctev_dest = HoleDest hole
                      , ctev_loc = loc
                      , ctev_rewriters = rewriters }
      co = HoleCo hole
  updTcRef ref (`snocBag` ct)
  whenDOptM Opt_D_dump_tc_trace $ do
    ctxt <- getErrCtxt
    doc <- mkErrInfo emptyTidyEnv ctxt
    traceTc "uKind_defer"
      $ vcat [ debugPprMonoKind ki1, debugPprMonoKind ki2, doc ]
    traceTc "uKind_defer2" (ppr co)

  return co

uKind :: UnifyEnv -> TcMonoKind -> TcMonoKind -> TcM KindCoercion
uKind env orig_ki1 orig_ki2 = do
  tclvl <- getTcLevel
  traceTc "u_kis"
    $ vcat [ text "tclvl" <+> ppr tclvl
           , sep [ ppr orig_ki1, text "~", ppr orig_ki2 ] ]
  co <- go orig_ki1 orig_ki2
  if isReflKiCo co
    then traceTc "u_kis yields no coercion" empty
    else traceTc "u_kis yields coercion:" (ppr co)
  return co
  where   
    go :: TcMonoKind -> TcMonoKind -> TcM KindCoercion
    go (KiVarKi kv1) ki2 = do
      lookup_res <- isFilledMetaKiVar_maybe kv1
      case lookup_res of
        Just ki1 -> do traceTc "found filled kivar" (ppr kv1 <+> text ":->" <+> ppr ki1)
                       uKind env ki1 orig_ki2
        Nothing -> uUnfilledKiVar env NotSwapped kv1 ki2

    go ki1 (KiVarKi kv2) = do
      lookup_res <- isFilledMetaKiVar_maybe kv2
      case lookup_res of
        Just ki2 -> do traceTc "found filled kivar" (ppr kv2 <+> text ":->" <+> ppr ki2)
                       uKind env orig_ki1 ki2
        Nothing -> uUnfilledKiVar env IsSwapped kv2 ki1

    go ki1@(KiConApp kc1 []) (KiConApp kc2 [])
      | kc1 == kc2
      = return $ mkReflKiCo ki1

    go (KiConApp kc1 kis1) (KiConApp kc2 kis2)
      | kc1 == kc2, equalLength kis1 kis2
      = do traceTc "go-kicon" (ppr kc1 $$ ppr kis1 $$ ppr kis2)
           cos <- zipWithM u_kc_arg kis1 kis2
           return $ mkKiConAppCo kc1 cos

    go (FunKi FKF_K_K arg1 res1) (FunKi FKF_K_K arg2 res2) = do
      co_l <- uKind env arg1 arg2
      co_r <- uKind env res1 res2
      return $ mkFunKiCo FKF_K_K co_l co_r 

    go ki1 ki2 = defer ki1 ki2

    ------------------
    defer ki1 ki2
      | ki1 `tcEqMonoKind` ki2 = return $ mkReflKiCo ki1
      | otherwise = uKind_defer env orig_ki1 orig_ki2

    ------------------
    u_kc_arg ki1 ki2 = do
      traceTc "u_tc_arg" (ppr ki1 $$ ppr ki2)
      uKind env_arg ki1 ki2
      where
        env_arg = env { u_loc = adjustCtLoc False True (u_loc env) }

{- *********************************************************************
*                                                                      *
                 uUnfilledVar and friends
*                                                                      *
********************************************************************* -}

uUnfilledKiVar :: UnifyEnv -> SwapFlag -> TcKiVar -> TcMonoKind -> TcM KindCoercion
uUnfilledKiVar env swapped kv1 ki2 = do
  ki2 <- liftZonkM $ zonkTcMonoKind ki2
  uUnfilledKiVar1 env swapped kv1 ki2

uUnfilledKiVar1 :: UnifyEnv -> SwapFlag -> TcKiVar -> TcMonoKind -> TcM KindCoercion
uUnfilledKiVar1 env swapped kv1 ki2
  | Just kv2 <- getKiVarMono_maybe ki2
  = go kv2
  | otherwise
  = uUnfilledKiVar2 env swapped kv1 ki2
  where
    go kv2
      | kv1 == kv2
      = return $ mkReflKiCo (mkKiVarMKi kv1)
      | swapOverKiVars False kv1 kv2
      = uUnfilledKiVar2 env (flipSwap swapped) kv2 (mkKiVarMKi kv1)
      | otherwise
      = uUnfilledKiVar2 env swapped kv1 ki2

uUnfilledKiVar2 :: UnifyEnv -> SwapFlag -> TcKiVar -> TcMonoKind -> TcM KindCoercion
uUnfilledKiVar2 env@(UE { u_defer = def_eq_ref }) swapped kv1 ki2 = do
  cur_lvl <- getTcLevel
  if not (touchabilityAndShapeTestKind cur_lvl kv1 ki2
          && simpleUnifyCheckKind kv1 ki2)
    then not_ok_so_defer
    else do traceTc "uUnfilledKiVar2 ok" $ vcat [ ppr kv1, ppr ki2 ]
            liftZonkM $ writeMetaKiVar kv1 ki2
            case u_unified env of
              Nothing -> return ()
              Just uref -> updTcRef uref (kv1 :)
            return $ mkReflKiCo ki2
  where
    ki1 = mkKiVarMKi kv1
    defer = unSwap swapped (uKind_defer env) ki1 ki2
    not_ok_so_defer = do
      traceTc "uUnfilledVar2 not ok" (ppr kv1 $$ ppr ki2)
      defer            

swapOverKiVars :: Bool -> TcKiVar -> TcKiVar -> Bool
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
    lvl1 = tcKiVarLevel kv1
    lvl2 = tcKiVarLevel kv2
    pri1 = lhsKiPriority kv1
    pri2 = lhsKiPriority kv2
    kv1_name = Var.varName kv1
    kv2_name = Var.varName kv2

lhsKiPriority :: TcKiVar -> Int
lhsKiPriority kv = assertPpr (isKiVar kv) (ppr kv) $
  case tcKiVarDetails kv of
    SkolemKv {} -> 0
    MetaKv { mkv_info = info } -> case info of
                                    KiVarKv -> 1
                                    TauKv -> 3

matchExpectedFunKind :: KindedThing -> Arity -> TcMonoKind -> TcM KindCoercion
matchExpectedFunKind cs_ty n k = go n k
  where
    go 0 k = return (mkReflKiCo k)
    go n k@(KiVarKi kvar)
      | isMetaKiVar kvar
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
      let new_fun = mkVisFunKis arg_kinds res_kind
          origin = KindEqOrigin { keq_actual = k
                                , keq_expected = new_fun
                                , keq_thing = Just cs_ty
                                , keq_visible = True
                                }
      unifyKindAndEmit origin k new_fun

{- *********************************************************************
*                                                                      *
                 Checking alpha ~ ki
              for the on-the-fly unifier
*                                                                      *
********************************************************************* -}

simpleUnifyCheckKind  :: TcKiVar -> TcMonoKind -> Bool
simpleUnifyCheckKind lhs_kv rhs = go_mono rhs
  where
    lhs_kv_lvl = tcKiVarLevel lhs_kv
    lhs_kv_is_concrete = isConcreteKiVar lhs_kv

    go_mono (KiVarKi kv)
      | lhs_kv == kv = False
      | tcKiVarLevel kv > lhs_kv_lvl = False
      | lhs_kv_is_concrete, not (isConcreteKiVar kv) = False
      | otherwise = True

    go_mono (FunKi { fk_f = af, fk_arg = a, fk_res = r })
      | af == FKF_C_K = False
      | otherwise = go_mono a && go_mono r

    go_mono (KiConApp _ kis) = all go_mono kis

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

okCheckReflKi :: TcMonoKind -> TcM (PuResult a Reduction)
okCheckReflKi ki = return $ PuOK emptyBag $ mkReflRednKi ki

failCheckWith :: CheckTyKiEqResult -> TcM (PuResult a b)
failCheckWith p = return $ PuFail p

mapCheck :: (x -> TcM (PuResult a Reduction)) -> [x] -> TcM (PuResult a Reductions)
mapCheck f xs = do
  ress <- mapM f xs
  return (unzipRedns <$> sequenceA ress)

data KiEqFlags = KEF
  { kef_foralls :: Bool -- always false: we work only on monokinds (can prob remove)
  , kef_lhs :: CanEqLHS
  , kef_unifying :: AreUnifying
  , kef_occurs :: CheckTyKiEqProblem
  }

data AreUnifying
  = UnifyingTy MetaInfo TcLevel LevelCheck
  | UnifyingKi MetaInfoK TcLevel LevelCheck
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
  ppr (UnifyingTy mi lvl lc) = text "UnifyingTy" <+> (braces
                               $ ppr mi <> comma <+> ppr lvl <> comma <+> ppr lc)
  ppr (UnifyingKi mi lvl lc) = text "UnifyingKi" <+> (braces
                               $ ppr mi <> comma <+> ppr lvl <> comma <+> ppr lc)

instance Outputable LevelCheck where
  ppr LC_None = text "LC_None"
  ppr LC_Check = text "LC_Check"
  ppr LC_Promote = text "LC_Promote"

checkKiEqRhs :: KiEqFlags -> TcMonoKind -> TcM (PuResult () Reduction)
checkKiEqRhs flags ki = case ki of
  KiConApp kc kis -> checkKiConApp flags ki kc kis
  KiVarKi kv -> checkKiVar flags kv
  FunKi { fk_f = af, fk_arg = a, fk_res = r }
    | FKF_C_K <- af
    , not (kef_foralls flags)
    -> failCheckWith impredicativeProblem
    | otherwise
    -> do a_res <- checkKiEqRhs flags a
          r_res <- checkKiEqRhs flags r
          return $ mkFunKiRedn af <$> a_res <*> r_res

checkKiConApp :: KiEqFlags -> TcMonoKind -> KiCon -> [TcMonoKind] -> TcM (PuResult () Reduction)
checkKiConApp flags kc_app kc kis
  = recurseIntoKiConApp flags kc kis

recurseIntoKiConApp :: KiEqFlags -> KiCon -> [TcMonoKind] -> TcM (PuResult () Reduction)
recurseIntoKiConApp flags kc kis = do
  kis_res <- mapCheck (checkKiEqRhs flags) kis
  return (mkKiConAppRedn kc <$> kis_res)

checkKiVar :: KiEqFlags -> TcKiVar -> TcM (PuResult () Reduction)
checkKiVar (KEF { kef_lhs = lhs, kef_unifying = unifying, kef_occurs = occ_prob }) occ_kv
  = case lhs of
      KiVarLHS lhs_kv -> check_kv unifying lhs_kv
  where
    lvl_occ = tcKiVarLevel occ_kv
    success = okCheckReflKi (mkKiVarMKi occ_kv)

    check_kv NotUnifying lhs_kv = simple_occurs_check lhs_kv
    check_kv (UnifyingKi info lvl prom) lhs_kv = do
      mb_done <- isFilledMetaKiVar_maybe occ_kv
      case mb_done of
        Just _ -> success
        Nothing -> check_unif info lvl prom lhs_kv
    check_kv (UnifyingTy {}) _ = panic "check_kv (UnifyingTy{})"

    check_unif :: MetaInfoK -> TcLevel -> LevelCheck -> TcKiVar -> TcM (PuResult a Reduction)
    check_unif lhs_kv_info lhs_kv_lvl prom lhs_kv
      | isConcreteInfoK lhs_kv_info
      , not (isConcreteKiVar occ_kv)
      = if can_make_concrete occ_kv
        then promote lhs_kv lhs_kv_info lhs_kv_lvl
        else failCheckWith (ctkeProblem ctkeConcrete)

      | lvl_occ `strictlyDeeperThan` lhs_kv_lvl
      = case prom of
          LC_None -> pprPanic "check_unif" (ppr lhs_kv $$ ppr occ_kv)
          LC_Check -> failCheckWith (ctkeProblem ctkeSkolemEscape)
          LC_Promote
            | isSkolemKiVar occ_kv -> failCheckWith (ctkeProblem ctkeSkolemEscape)
            | otherwise -> promote lhs_kv lhs_kv_info lhs_kv_lvl
      | otherwise
      = simple_occurs_check lhs_kv

    simple_occurs_check lhs_kv
      | lhs_kv == occ_kv
      = failCheckWith (ctkeProblem occ_prob)
      | otherwise
      = success

    can_make_concrete occ_kv = case tcKiVarDetails occ_kv of
      MetaKv { mkv_info = info } -> case info of
                                      TauKv {} -> True
                                      _ -> False
      _ -> False

    promote lhs_kv lhs_kv_info lhs_kv_lvl
      | MetaKv { mkv_info = info_occ, mkv_tclvl = lvl_occ } <- tcKiVarDetails occ_kv
      = do let new_info | isConcreteInfoK lhs_kv_info = lhs_kv_info
                        | otherwise = info_occ
               new_lvl = lhs_kv_lvl `minTcLevel` lvl_occ

           new_kv_ki <- promote_meta_kivar new_info new_lvl occ_kv
           okCheckReflKi new_kv_ki
      | otherwise = pprPanic "promote" (ppr occ_kv)

promote_meta_kivar :: MetaInfoK -> TcLevel -> TcKiVar -> TcM TcMonoKind
promote_meta_kivar info dest_lvl occ_kv = do
  mb_filled <- isFilledMetaKiVar_maybe occ_kv
  case mb_filled of
    Just ki -> return ki
    Nothing -> do new_kv <- cloneMetaKiVarWithInfo info dest_lvl occ_kv
                  liftZonkM $ writeMetaKiVar occ_kv (mkKiVarMKi new_kv)
                  traceTc "promoteKiVar" (ppr occ_kv <+> text "-->" <+> ppr new_kv)
                  return $ mkKiVarMKi new_kv

touchabilityAndShapeTestKind :: TcLevel -> TcKiVar -> TcMonoKind -> Bool
touchabilityAndShapeTestKind given_eq_lvl kv rhs
  | MetaKv { mkv_info = info, mkv_tclvl = kv_lvl } <- tcKiVarDetails kv
  , checkTopShapeKind info rhs
  = kv_lvl `deeperThanOrSame` given_eq_lvl
  | otherwise
  = False

checkTopShapeKind :: MetaInfoK -> TcMonoKind -> Bool
checkTopShapeKind info xi
  = case info of
      KiVarKv -> case getKiVarMono_maybe xi of
                   Nothing -> False
                   Just kv -> case tcKiVarDetails kv of
                                SkolemKv {} -> True
                                MetaKv { mkv_info = KiVarKv } -> True
                                _ -> False
      _ -> True
