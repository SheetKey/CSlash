{-# LANGUAGE BangPatterns #-}

module CSlash.Tc.Solver.Equality (solveKiCoercion, solveTyEquality) where

import CSlash.Tc.Solver.Irred( solveIrredTy, solveIrredKi )
-- import GHC.Tc.Solver.Dict( matchLocalInst, chooseInstance )
import CSlash.Tc.Solver.Rewrite
import CSlash.Tc.Solver.Monad
import CSlash.Tc.Solver.InertSet
-- import GHC.Tc.Solver.Types( findFunEqsByTyCon )
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.Unify
import CSlash.Tc.Utils.TcType
-- import GHC.Tc.Instance.Family ( tcTopNormaliseNewTypeTF_maybe )
-- import GHC.Tc.Instance.FunDeps( FunDepEqn(..) )
import qualified CSlash.Tc.Utils.Monad as TcM

import CSlash.Core.Type
import CSlash.Core.Type.Compare
import CSlash.Core.Type.FVs
import CSlash.Core.Type.Subst
import CSlash.Core.Kind
import CSlash.Core.Kind.Compare
import CSlash.Core.Predicate
import CSlash.Core.Kind.Subst
-- import GHC.Core.Class
import CSlash.Core.DataCon ( dataConName )
import CSlash.Core.TyCon
import CSlash.Core.Type.Rep
-- import GHC.Core.Coercion
-- import GHC.Core.Coercion.Axiom
import CSlash.Core.Reduction
-- import GHC.Core.Unify( tcUnifyTyWithTFs )
-- import GHC.Core.FamInstEnv ( FamInstEnvs, FamInst(..), apartnessCheck
--                            , lookupFamInstEnvByTyCon )
import CSlash.Core

import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set( anyVarSet, unionVarSet, mapVarSet )
import CSlash.Types.Name.Reader
import CSlash.Types.Basic

-- import CSlash.Builtin.Types ( anyTypeOfKind )

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc
import CSlash.Utils.Monad
import CSlash.Utils.Constants( debugIsOn )

import CSlash.Data.Pair
import CSlash.Data.Bag
import Control.Monad
import Data.Maybe ( isJust, isNothing )
import Data.List  ( zip4 )

import qualified Data.Semigroup as S
import Data.Bifunctor ( bimap )
import Data.Void( Void )

{- *********************************************************************
*                                                                      *
*        Equalities
*                                                                      *
********************************************************************* -}

solveTyEquality :: CtTyEvidence -> AnyType -> AnyType -> TySolverStage Void
solveTyEquality ev ty1 ty2 = do
  Pair ty1' ty2' <- zonkEqTypes ev ty1 ty2
  mb_canon <- canonicalizeTyEquality ev ty1' ty2'
  case mb_canon of
    Left irred_ct -> do tryQCsIrredTyEqCt irred_ct
                        solveIrredTy irred_ct
    Right eq_ct -> do tryInertTyEqs eq_ct
                      tryQCsTyEqCt eq_ct
                      simpleStage (updInertTyEqs eq_ct)
                      stopWithStage (tyEqCtEvidence eq_ct) "Kept inert EqCt"

updInertTyEqs :: TyEqCt -> TcS ()
updInertTyEqs eq_ct = do
  kickOutRewritableTy (TKOAfterAdding (tyEqCtLHS eq_ct)) (tyEqCtFlavor eq_ct)
  tc_lvl <- getTcLevel
  updInertTyCans (addTyEqToCans tc_lvl eq_ct)

solveKiCoercion :: CtKiEvidence -> KiPredCon -> AnyMonoKind -> AnyMonoKind -> KiSolverStage Void
solveKiCoercion ev rel ki1 ki2 = do
  Pair ki1' ki2' <- if rel /= LTKi
                    then zonkEqKinds ev ki1 ki2
                    else return $ Pair ki1 ki2
  let ev' | debugIsOn = setCtEvPredKind ev $ mkKiCoPred rel ki1' ki2'
          | otherwise = ev

  mb_canon <- canonicalizeKiCoercion ev' rel ki1' ki2'

  case mb_canon of
    Left irred_ct -> do tryQCsIrredKiCoCt irred_ct
                        solveIrredKi irred_ct
    Right kico_ct -> do tryInertKiCos kico_ct
                        tryQCsKiCoCt kico_ct
                        simpleStage (updInertKiCos kico_ct)
                        stopWithStage (kiCoCtEvidence kico_ct) "Kept inert EqCt"

updInertKiCos :: KiCoCt -> TcS ()
updInertKiCos kico_ct = do
  kickOutRewritable (KOAfterAdding (kiCoCtLHS kico_ct)) (kiCoCtFlavor kico_ct)
  tc_lvl <- getTcLevel
  updInertKiCans (addKiCoToCans tc_lvl kico_ct)

{- *********************************************************************
*                                                                      *
*           zonkEqTypes
*                                                                      *
********************************************************************* -}

zonkEqTypes :: CtTyEvidence -> AnyType -> AnyType -> TySolverStage (Pair AnyType)
zonkEqTypes ev ty1 ty2 = Stage $ do
  res <- go ty1 ty2
  case res of
    Left pair -> continueWith pair
    Right ty -> canTyEqReflexive ev ty
  where
    go :: AnyType -> AnyType -> TcS (Either (Pair AnyType) AnyType)
    go (TyVarTy tv1) (TyVarTy tv2) = tyvar_tyvar tv1 tv2
    go (TyVarTy tv1) ty2 = tyvar NotSwapped tv1 ty2
    go ty1 (TyVarTy tv2) = tyvar IsSwapped tv2 ty1

    go (FunTy k1 arg1 res1) (FunTy k2 arg2 res2)
      | eqMonoKind k1 k2
      = do res_a <- go arg1 arg2
           res_b <- go res1 res2
           return $ combine_rev (FunTy k1) res_b res_a
           
    go ty1@(FunTy {}) ty2 = bale_out ty1 ty2
    go ty1 ty2@(FunTy {}) = bale_out ty1 ty2

    go ty1 ty2
      | Just (tc1, tys1) <- splitTyConAppNoView_maybe ty1
      , Just (tc2, tys2) <- splitTyConAppNoView_maybe ty2
      = if tc1 == tc2 && tys1 `equalLength` tys2
        then tycon tc1 tys1 tys2
        else bale_out ty1 ty2

    go ty1 ty2
      | Just (ty1a, ty1b) <- tcSplitAppTyNoView_maybe ty1
      , Just (ty2a, ty2b) <- tcSplitAppTyNoView_maybe ty2
      = do res_a <- go ty1a ty2a
           res_b <- go ty1b ty2b
           return $ combine_rev mkAppTy res_b res_a

    go ty1 ty2 = bale_out ty1 ty2

    bale_out ty1 ty2 = return $ Left (Pair ty1 ty2)

    tyvar :: SwapFlag -> AnyTyVar AnyKiVar -> AnyType -> TcS (Either (Pair AnyType) AnyType)
    tyvar swapped tv ty = case handleAnyTv (const Nothing) (Just . tcVarDetails) tv of
      Just (MetaVar { mv_ref = ref }) -> do
        cts <- readTcRef ref
        case cts of
          Flexi -> give_up
          Indirect ty' -> do trace_indirect tv ty'
                             unSwap swapped go ty' ty
      _ -> give_up
      where
        give_up = return $ Left $ unSwap swapped Pair (mkTyVarTy tv) ty

    tyvar_tyvar tv1 tv2
      | tv1 == tv2 = return (Right (mkTyVarTy tv1))
      | otherwise = do (ty1', progress1) <- quick_zonk tv1
                       (ty2', progress2) <- quick_zonk tv2
                       if progress1 || progress2
                         then go ty1' ty2'
                         else return $ Left (Pair (mkTyVarTy tv1) (mkTyVarTy tv2))

    trace_indirect tv ty = traceTcS "Following filled tyvar (zonk_eq_types)"
                           (ppr tv <+> equals <+> ppr ty)

    quick_zonk tv = case handleAnyTv (const Nothing) (Just . tcVarDetails) tv of
      Just (MetaVar { mv_ref = ref }) -> do
        cts <- readTcRef ref
        case cts of
          Flexi -> return (TyVarTy tv, False)
          Indirect ty' -> do trace_indirect tv ty'
                             return (ty', True)
      _ -> return (TyVarTy tv, False)

    tycon :: AnyTyCon -> [AnyType] -> [AnyType] -> TcS (Either (Pair AnyType) AnyType)
    tycon tc tys1 tys2 = do
      results <- zipWithM go tys1 tys2
      return $ case combine_results results of
        Left tys -> Left (mkTyConApp tc <$> tys)
        Right tys -> Right (mkTyConApp tc tys)

    combine_results :: [Either (Pair AnyType) AnyType] -> Either (Pair [AnyType]) [AnyType]
    combine_results = bimap (fmap reverse) reverse .
                      foldl' (combine_rev (:)) (Right [])

    combine_rev :: (a -> b -> c) -> Either (Pair b) b -> Either (Pair a) a -> Either (Pair c) c
    combine_rev f (Left list) (Left elt) = Left (f <$> elt <*> list)
    combine_rev f (Left list) (Right ty) = Left (f <$> pure ty <*> list)
    combine_rev f (Right tys) (Left elt) = Left (f <$> elt <*> pure tys)
    combine_rev f (Right tys) (Right ty) = Right (f ty tys)

{- *********************************************************************
*                                                                      *
*           zonkEqKinds
*                                                                      *
********************************************************************* -}

zonkEqKinds :: CtKiEvidence -> AnyMonoKind -> AnyMonoKind -> KiSolverStage (Pair AnyMonoKind)
zonkEqKinds ev ki1 ki2 = Stage $ do
  res <- go_mono ki1 ki2
  case res of
    Left pair -> continueWith pair
    Right ki -> canKiCoReflexive ev ki
  where
    go_mono :: AnyMonoKind -> AnyMonoKind -> TcS (Either (Pair AnyMonoKind) AnyMonoKind)
    go_mono (KiVarKi kv1) (KiVarKi kv2) = kivar_kivar kv1 kv2
    go_mono (KiVarKi kv1) ki2 = kivar NotSwapped kv1 ki2
    go_mono ki1 (KiVarKi kv2) = kivar IsSwapped kv2 ki1

    go_mono ki1@(BIKi kc1) (BIKi kc2)
      | kc1 == kc2
      = return $ Right ki1

    go_mono (FunKi f1 arg1 res1) (FunKi f2 arg2 res2)
      | f1 == f2
      = do res_a <- go_mono arg1 arg2
           res_b <- go_mono res1 res2
           return $ combine_rev (FunKi f1) res_b res_a
    go_mono ki1 ki2 = bale_out ki1 ki2

    bale_out ki1 ki2 = return $ Left (Pair ki1 ki2)

    kivar :: SwapFlag -> AnyKiVar -> AnyMonoKind -> TcS (Either (Pair AnyMonoKind) AnyMonoKind)
    kivar swapped kv ki = case handleAnyKv (const Nothing) (Just . tcVarDetails) kv of
      Just (MetaVar { mv_ref = ref }) -> do
        cts <- readTcRef ref
        case cts of
          Flexi -> give_up
          Indirect ki' -> do
            trace_indirect kv ki'
            unSwap swapped go_mono ki' ki
      _ -> give_up
      where
        give_up = return $ Left $ unSwap swapped Pair (mkKiVarKi kv) ki

    kivar_kivar kv1 kv2
      | kv1 == kv2 = return $ Right (mkKiVarKi kv1)
      | otherwise = do (ki1', progress1) <- quick_zonk kv1
                       (ki2', progress2) <- quick_zonk kv2
                       if progress1 || progress2
                         then go_mono ki1' ki2'
                         else return $ Left (Pair (KiVarKi kv1) (KiVarKi kv2))

    trace_indirect kv ki
      = traceTcS "Following filled kivar (zonkEqKinds)"
                 (ppr kv <+> equals <+> ppr ki)

    quick_zonk kv = case handleAnyKv (const Nothing) (Just . tcVarDetails) kv of
      Just (MetaVar { mv_ref = ref }) -> do
        cts <- readTcRef ref
        case cts of
          Flexi -> return (KiVarKi kv, False)
          Indirect ki' -> do trace_indirect kv ki'
                             return (ki', True)
      _ -> return (KiVarKi kv, False)

    combine_results :: [Either (Pair AnyMonoKind) AnyMonoKind]
                    -> Either (Pair [AnyMonoKind]) [AnyMonoKind]
    combine_results = bimap (fmap reverse) reverse .
                      foldl' (combine_rev (:)) (Right [])
                      
    combine_rev :: (a -> b -> c) -> Either (Pair b) b -> Either (Pair a) a -> Either (Pair c) c
    combine_rev f (Left list) (Left elt) = Left (f <$> elt <*> list)
    combine_rev f (Left list) (Right ki) = Left (f <$> pure ki <*> list)
    combine_rev f (Right kis) (Left elt) = Left (f <$> elt <*> pure kis)
    combine_rev f (Right kis) (Right ki) = Right (f ki kis)

{- *********************************************************************
*                                                                      *
*           canonicaliseTyEquality
*                                                                      *
********************************************************************* -}

canonicalizeTyEquality
  :: CtTyEvidence
  -> AnyType
  -> AnyType
  -> TySolverStage (Either IrredTyCt TyEqCt)
canonicalizeTyEquality ev ty1 ty2 = Stage $ do
  traceTcS "canonicalizeTyEquality"
    $ vcat [ ppr ev, ppr ty1, ppr ty2 ]

  rdr_env <- getGlobalRdrEnvTcS
  can_ty_eq_nc False rdr_env ev ty1 ty1 ty2 ty2

can_ty_eq_nc
  :: Bool
  -> GlobalRdrEnv
  -> CtTyEvidence
  -> AnyType -> AnyType
  -> AnyType -> AnyType
  -> TcS (StopOrContinueTy (Either IrredTyCt TyEqCt))

can_ty_eq_nc _ _ ev ty1@(TyConApp tc1 []) _ (TyConApp tc2 []) _
  | tc1 == tc2
  = canTyEqReflexive ev ty1

can_ty_eq_nc rewritten rdr_env ev ty1 ps_ty1 ty2 ps_ty2
  | Just ty1' <- coreView ty1 = can_ty_eq_nc rewritten rdr_env ev ty1' ps_ty1 ty2 ps_ty2
  | Just ty2' <- coreView ty2 = can_ty_eq_nc rewritten rdr_env ev ty1 ps_ty1 ty2' ps_ty2

can_ty_eq_nc rewritten rdr_env ev (CastTy ty1 kco1) _ ty2 ps_ty2
  | isNothing (canTyEqLHS_maybe ty2)
  = canTyEqCast rewritten rdr_env ev NotSwapped ty1 kco1 ty2 ps_ty2

can_ty_eq_nc rewritten rdr_env ev ty1 ps_ty1 (CastTy ty2 kco2) _
  | isNothing (canTyEqLHS_maybe ty1)
  = canTyEqCast rewritten rdr_env ev IsSwapped ty2 kco2 ty1 ps_ty1

----------------------
-- Otherwise try to decompose
----------------------

can_ty_eq_nc _ _ ev
  ty1@(FunTy ki1 ty1a ty1b) _
  ty2@(FunTy ki2 ty2a ty2b) _
  = canDecomposableFunTy ev (ty1, ki1, ty1a, ty1b) (ty2, ki2, ty2a, ty2b)

can_ty_eq_nc rewritten _ ev ty1 _ ty2 _
  | Just (tc1, tys1) <- tcSplitTyConApp_maybe ty1
  , Just (tc2, tys2) <- tcSplitTyConApp_maybe ty2
  , let both_generative = isGenerativeTyCon tc1 && isGenerativeTyCon tc2
  , rewritten || both_generative
  = canTyConApp ev both_generative (ty1, tc1, tys1) (ty2, tc2, tys2)

can_ty_eq_nc _ _ ev s1@ForAllTy{} _ s2@ForAllTy{} _
  = can_ty_eq_nc_forall ev s1 s2

can_ty_eq_nc True _ ev ty1 _ ty2 _
  | Just (t1, s1) <- tcSplitAppTy_maybe ty1
  , Just (t2, s2) <- tcSplitAppTy_maybe ty2
  = can_ty_eq_app ev t1 s1 t2 s2

-------------------
-- Can't decompose.
-------------------

can_ty_eq_nc False rdr_env ev _ ps_ty1 _ ps_ty2 = do
  (redn1@(TyReduction _ xi1), rewriters1, _) <- rewriteTy ev ps_ty1
  (redn2@(TyReduction _ xi2), rewriters2, _) <- rewriteTy ev ps_ty2
  new_ev <- rewriteTyEqEvidence (rewriters1 S.<> rewriters2) ev NotSwapped redn1 redn2
  traceTcS "can_ty_eq_nc: go round again" (ppr new_ev $$ ppr xi1 $$ ppr xi2)
  can_ty_eq_nc True rdr_env new_ev xi1 xi1 xi2 xi2

----------------------------
-- Look for a canonical LHS.
-- Only rewritten types end up below here.
----------------------------

can_ty_eq_nc True _ ev ty1 ps_ty1 ty2 ps_ty2
  | Just can_eq_lhs1 <- canTyEqLHS_maybe ty1
  = do traceTcS "can_eq1" (ppr ty1 $$ ppr ty2)
       canTyEqCanLHS ev NotSwapped can_eq_lhs1 ps_ty1 ty2 ps_ty2

  | Just can_eq_lhs2 <- canTyEqLHS_maybe ty2
  = do traceTcS "can_eq2" (ppr ty1 $$ ppr ty2)
       canTyEqCanLHS ev IsSwapped can_eq_lhs2 ps_ty2 ty1 ps_ty1

----------------------------
-- Fall-through. Give up.
----------------------------

can_ty_eq_nc True _ ev _ ps_ty1 _ ps_ty2 = do
  traceTcS "can_ty_eq_nc catch-all case" (ppr ps_ty1 $$ ppr ps_ty2)
  finishCanWithIrredTy ShapeMismatchReason ev

can_ty_eq_nc_forall
  :: CtTyEvidence
  -> AnyType
  -> AnyType
  -> TcS (StopOrContinueTy (Either IrredTyCt TyEqCt))

can_ty_eq_nc_forall ev s1 s2
  | CtTyWanted { cttev_dest = orig_dest } <- ev
  = do let (bndrs1, phi1, bndrs2, phi2) = split_foralls s1 s2
           flags1 = binderFlags bndrs1
           flags2 = binderFlags bndrs2

       if not (all2 eqForAllVis flags1 flags2)
         then do traceTcS "Forall failure: visibility-mismatch"
                   $ vcat [ ppr s1, ppr s2
                          , ppr bndrs1, ppr bndrs2
                          , ppr flags1, ppr flags2 ]
                 canTyEqHardFailure ev s1 s2
         else do traceTcS "Creating implication for polytype equality" (ppr ev)
                 let (free_tvs, free_kcvs, free_kvs) = varsOfTypes [s1, s2]
                     empty_subst1 = mkEmptyTvSubst ( mkInScopeSet $ free_tvs `unionVarSet`
                                                     mapVarSet toAnyTyVar free_kcvs
                                                   , mkInScopeSet free_kvs )
                 skol_info <- mkSkolemInfo (UnifyForAllSkol phi1)
                 (subst1, skol_tvs) <- tcInstSkolTyVarsX skol_info empty_subst1
                                       $ binderVars bndrs1

                 let phi1' = substTy subst1 phi1

                     go :: UnifyEnv
                        -> [TcTyVar AnyKiVar]
                        -> AnyTvSubst
                        -> [AnyTyVarBinder]
                        -> [AnyTyVarBinder]
                        -> TcM.TcM AnyTypeCoercion
                     go uenv (skol_tv:skol_tvs) subst2@(TvSubst _ _ kvsubst2)
                       (bndr1:bndrs1) (bndr2:bndrs2) = do
                       let tv2 = binderVar bndr2
                           vis1 = binderFlag bndr1
                           vis2 = binderFlag bndr2
                       kco <- uKind uenv EQKi (varKind skol_tv)
                              (substMonoKi kvsubst2 (varKind tv2))

                       let subst2' = extendTvSubstAndInScope subst2 tv2
                                     (mkCastTy (mkTyVarTy $ toAnyTyVar skol_tv) kco)

                       co <- go uenv skol_tvs subst2' bndrs1 bndrs2

                       return $ panic "mkNakedForAllCo skol_tv vis1 vis2 kco co"

                     go uenv [] subst2 bndr1 bndr2
                       = assert (null bndrs1 && null bndrs2)
                         $ uType uenv phi1' (substTyUnchecked subst2 phi2)

                     go _ _ _ _ _ = panic "can_ty_eq_nc_forall"

                     init_subst2 = mkEmptyTvSubst (getTvSubstInScope subst1)

                 (lvl, (all_co, wanteds)) <- pushLevelNoWorkList (ppr skol_info)
                                             $ panic "unifyForAllBody ev"
                                             $ \uenv ->
                                                 go uenv skol_tvs init_subst2 bndrs1 bndrs2
                                                                      
                 emitTvImplicationTcS lvl (getSkolemInfo skol_info) skol_tvs wanteds

                 setWantedTyCo orig_dest all_co
                 stopWith ev "Deferred polytype equality"
  | otherwise
  = do traceTcS "Omitting decomposition of given polytype equality"
         $ pprEq s1 s2
       stopWith ev "Discard given polytype equality"
  where
    split_foralls :: AnyType -> AnyType -> ([AnyTyVarBinder], AnyType, [AnyTyVarBinder], AnyType)
    split_foralls  s1 s2
      | Just (bndr1, s1') <- splitForAllForAllTyBinder_maybe s1
      , Just (bndr2, s2') <- splitForAllForAllTyBinder_maybe s2
      = let !(bndrs1, phi1, bndrs2, phi2) = split_foralls s1' s2'
        in (bndr1:bndrs1, phi1, bndr2:bndrs2, phi2)
    split_foralls s1 s2 = ([], s1, [], s2)

can_ty_eq_app
  :: CtTyEvidence
  -> AnyType -> AnyType
  -> AnyType -> AnyType
  -> TcS (StopOrContinueTy (Either IrredTyCt TyEqCt))
can_ty_eq_app ev s1 t1 s2 t2
  | CtTyWanted { cttev_dest = dest } <- ev
  = do traceTcS "can_ty_eq_app"
         $ vcat [ text "s1:" <+> ppr s1, text "t1:" <+> ppr t1
                , text "s2:" <+> ppr s2, text "t2:" <+> ppr t2
                , text "vis:" <+> ppr (isNextArgVisible s1) ]
       (co, _, _, _, _) <- wrapTyUnifierTcS ev $ \uenv -> do
         let arg_env = updUEnvLoc uenv (adjustCtLoc (isNextArgVisible s1) False)
         co_t <- uType arg_env t1 t2
         co_s <- uType uenv s1 s2
         return $ mkAppCo co_s co_t
       setWantedTyCo dest co
       stopWith ev "Decomposed [W] AppTy"

  | s1k `mismatches` s2k
  = canTyEqHardFailure ev (s1 `mkAppTy` t1) (s2 `mkAppTy` t2)

  | CtTyGiven { cttev_covar = covar } <- ev
  = do let co = mkTyCoVarCo covar
           co_s = mkLRTyCo CLeft co
           co_t = mkLRTyCo CRight co
       covar_s <- newGivenTyCoVar loc (mkTyEqPred s1 s2)
       covar_t <- newGivenTyCoVar loc (mkTyEqPred t1 t2)
       emitTyWorkNC [covar_t]
       startAgainWith (mkNonCanonicalTy covar_s)

  where
    loc = ctEvLoc ev

    s1k = typeKind s1
    s2k = typeKind s2

    k1 `mismatches` k2
      = isForAllKi k1 && not (isForAllKi k2)
        || not (isForAllKi k1) && isForAllKi k2

canTyEqCast
  :: Bool
  -> GlobalRdrEnv
  -> CtTyEvidence
  -> SwapFlag
  -> AnyType -> AnyKindCoercion
  -> AnyType -> AnyType
  -> TcS (StopOrContinueTy (Either IrredTyCt TyEqCt))
canTyEqCast rewritten rdr_env ev swapped ty1 kco1 ty2 ps_ty2 = do
  traceTcS "Decomposing cast"
    $ vcat [ ppr ev
           , ppr ty1 <+> text "|>" <+> ppr kco1
           , ppr ps_ty2 ]
  new_ev <- rewriteTyEqEvidence emptyTyRewriterSet ev swapped
            (mkGReflLeftRednTy ty1 kco1)
            (mkReflRednTy ps_ty2)
  can_ty_eq_nc rewritten rdr_env new_ev ty1 ty1 ty2 ps_ty2

canTyConApp
  :: CtTyEvidence
  -> Bool
  -> (AnyType, AnyTyCon, [AnyType])
  -> (AnyType, AnyTyCon, [AnyType])
  -> TcS (StopOrContinueTy (Either IrredTyCt TyEqCt))
canTyConApp ev both_generative (ty1, tc1, tys1) (ty2, tc2, tys2)
  | tc1 == tc2
  , tys1 `equalLength` tys2
  = do inerts <- getInertTySet
       if can_decompose inerts
         then canDecomposableTyConAppOK ev tc1 (ty1, tys1) (ty2, tys2)
         else canTyEqSoftFailure ev ty1 ty2

  | otherwise
  = if both_generative
    then canTyEqHardFailure ev ty1 ty2
    else canTyEqSoftFailure ev ty1 ty2
  where
    can_decompose inerts
      = isInjectiveTyCon tc1
        || panic "canTyConApp failure"

canDecomposableTyConAppOK
  :: CtTyEvidence
  -> AnyTyCon
  -> (AnyType, [AnyType])
  -> (AnyType, [AnyType])
  -> TcS (StopOrContinueTy a)
canDecomposableTyConAppOK ev tc (ty1, tys1) (ty2, tys2)
  = assert (tys1 `equalLength` tys2) $ do
  traceTcS "canDecomposableTyConAppOK"
    $ vcat [ ppr ev, ppr tc, ppr tys1, ppr tys2 ]

  case ev of
    CtTyWanted { cttev_dest = dest }
      -> do (co, _, _, _, _) <- wrapTyUnifierTcS ev $ \uenv -> do
              cos <- zipWith3M (u_arg uenv) new_locs tys1 tys2
              return (mkTyConAppCo tc cos)
            setWantedTyCo dest co

    CtTyGiven { cttev_covar = covar }
      | let pred_ty = mkTyEqPred ty1 ty2
            ev_co = mkTyCoVarCo (setVarType covar pred_ty)
        -> emitNewTyGivens loc (panic "canDecomposableTyConAppOK")
           -- [ (mkSelCo (SelTyCon i) ev_co)
           -- | (ty1, ty2, i) <- zip3 tys1 tys2 [0..]
           -- , not (isKiCoType ty1) && not (isKiCoType ty2) ]

  stopWith ev "Decomposed TyConApp"
  where
    loc = ctEvLoc ev

    u_arg uenv arg_loc = uType arg_env
      where arg_env = uenv `updUEnvLoc` const arg_loc

    new_locs = repeat loc -- THIS MIGHT LEAD TO BAD ERROR MESSAGES

canDecomposableFunTy
  :: CtTyEvidence
  -> (AnyType, AnyMonoKind, AnyType, AnyType)
  -> (AnyType, AnyMonoKind, AnyType, AnyType)
  -> TcS (StopOrContinueTy a)
canDecomposableFunTy ev f1@(ty1, k1, a1, r1) f2@(ty2, k2, a2, r2) = do
  traceTcS "canDecomposableFunTy"
    $ vcat [ ppr ev , ppr f1, ppr f2 ]
  case ev of
    CtTyWanted { cttev_dest = dest }
      -> do (co, _, _, _, _) <- wrapTyUnifierTcS ev $ \uenv ->
              do let ki_env = uenv `updUEnvLoc` toInvisibleLoc
                 ki <- uKind ki_env EQKi k1 k2
                 arg <- uType uenv a1 a2
                 res <- uType uenv r1 r2
                 return $ mkTyFunCo ki arg res
            setWantedTyCo dest co
    CtTyGiven { cttev_covar = covar }
      -> let pred_ty = mkTyEqPred ty1 ty2
             ev_co = mkTyCoVarCo (setVarType covar pred_ty)
         in emitNewTyGivens loc (panic "[ mkSelCo (SelFun fs) ev_co")
                                --  | fs <- [SelKind, SelArg, SelRes] ]
  stopWith ev "Decomposed FunTyConApp"
  where
    loc = ctEvLoc ev

canTyEqSoftFailure
  :: CtTyEvidence
  -> AnyType
  -> AnyType
  -> TcS (StopOrContinueTy (Either IrredTyCt a))
canTyEqSoftFailure ev ty1 ty2 = canTyEqHardFailure ev ty1 ty2

canTyEqHardFailure
  :: CtTyEvidence
  -> AnyType
  -> AnyType
  -> TcS (StopOrContinueTy (Either IrredTyCt a))
canTyEqHardFailure ev ty1 ty2 = do
  traceTcS "canTyEqHardFailure" (ppr ty1 $$ ppr ty2)
  (redn1, ty_rewriters1, ki_rewriters1) <- rewriteTyForErrors ev ty1
  (redn2, ty_rewriters2, ki_rewriters2) <- rewriteTyForErrors ev ty2
  traceTcS "canTyEqHardFailure ************************* DISCARDING ki_rewriters"
    $ vcat [ text "ki_rewriters1 =" <+> ppr ki_rewriters1
           , text "ki_rewriters2 =" <+> ppr ki_rewriters2 ]
  new_ev <- rewriteTyEqEvidence (ty_rewriters1 S.<> ty_rewriters2) ev NotSwapped redn1 redn2
  finishCanWithIrredTy ShapeMismatchReason new_ev

canTyEqCanLHS
  :: CtTyEvidence
  -> SwapFlag
  -> CanTyEqLHS
  -> AnyType
  -> AnyType
  -> AnyType
  -> TcS (StopOrContinueTy (Either IrredTyCt TyEqCt))
canTyEqCanLHS ev swapped lhs1 ps_xi1 xi2 ps_xi2
  | k1 `tcEqMonoKind` k2
  = canTyEqCanLHSHomo ev swapped lhs1 ps_xi1 xi2 ps_xi2
  | otherwise
  = canTyEqCanLHSHetero ev swapped lhs1 ps_xi1 k1 xi2 ps_xi2 k2
  where
    k1 = canTyEqLHSKind lhs1
    k2 = typeMonoKind xi2

canTyEqCanLHSHetero
  :: CtTyEvidence
  -> SwapFlag
  -> CanTyEqLHS -> AnyType -> AnyMonoKind
  -> AnyType -> AnyType -> AnyMonoKind
  -> TcS (StopOrContinueTy (Either IrredTyCt TyEqCt))
canTyEqCanLHSHetero ev swapped lhs1 ps_xi1 ki1 xi2 ps_xi2 ki2 = do
  (kind_co, rewriters, unif_happened) <- mk_kind_eq
  traceTcS "canTyEqCanLHSHetero DROPPING KI_REWRITERS **************************************"
    (ppr rewriters)
  if unif_happened
    then startAgainWith $ mkNonCanonicalTy ev
    else do let lhs_redn = mkReflRednTy ps_xi1
                mb_sym_kind_co = case swapped of
                                   NotSwapped -> mkSymKiCo kind_co
                                   IsSwapped -> kind_co
                rhs_redn = mkGReflRightRednTy xi2 mb_sym_kind_co
            traceTcS "Hetero equality gives rise to kind equality"
              (ppr swapped $$
               ppr kind_co <+> colon <+> sep [ ppr ki1, text "~", ppr ki2 ])
            type_ev <- rewriteTyEqEvidence emptyTyRewriterSet ev swapped lhs_redn rhs_redn

            let new_xi2 = mkCastTy ps_xi2 mb_sym_kind_co
            canTyEqCanLHSHomo type_ev NotSwapped lhs1 ps_xi1 new_xi2 new_xi2
  where
    xi1 = canTyEqLHSType lhs1

    mk_kind_eq :: TcS (AnyKindCoercion, KiRewriterSet, Bool)
    mk_kind_eq = case ev of
      CtTyGiven {} -> do
        let pred_ki = unSwap swapped (mkKiCoPred EQKi) ki1 ki2
            kind_loc = mkKindEqLoc xi1 xi2 (ctEvLoc ev)
        kind_ev <- newGivenKiCoVar kind_loc pred_ki
        emitKiWorkNC [kind_ev]
        return (ctEvKiCoercion kind_ev, emptyKiRewriterSet, False)

      CtTyWanted {} -> do
        (kind_co, tycts, kicts, tyunifs, kiunifs) <- wrapTyUnifierTcS ev $ \uenv ->
          let uenv' = updUEnvLoc uenv (mkKindEqLoc xi1 xi2)
          in unSwap swapped (uKind uenv' EQKi) ki1 ki2
        massertPpr (null tycts) (text "mk_kind_eq" <+> ppr tycts)
        massertPpr (null tyunifs) (text "mk_kind_eq" <+> ppr tyunifs)
        return (kind_co, kiRewriterSetFromCts kicts, not (null kiunifs))

canTyEqCanLHSHomo
  :: CtTyEvidence
  -> SwapFlag
  -> CanTyEqLHS -> AnyType
  -> AnyType -> AnyType
  -> TcS (StopOrContinueTy (Either IrredTyCt TyEqCt))
canTyEqCanLHSHomo ev swapped lhs1 ps_xi1 xi2 ps_xi2
  | (xi2', mkco) <- split_cast_ty xi2
  , Just lhs2 <- canTyEqLHS_maybe xi2'
  = canTyEqCanLHS2 ev swapped lhs1 ps_xi1 lhs2 (ps_xi2 `mkCastTyMCo` mkSymMKiCo mkco) mkco
  | otherwise
  = canTyEqCanLHSFinish ev swapped lhs1 ps_xi2
  where
    split_cast_ty (CastTy ty kco) = (ty, Just kco)
    split_cast_ty ty = (ty, Nothing)

canTyEqCanLHS2
  :: CtTyEvidence
  -> SwapFlag
  -> CanTyEqLHS -> AnyType
  -> CanTyEqLHS -> AnyType
  -> Maybe AnyKindCoercion
  -> TcS (StopOrContinueTy (Either IrredTyCt TyEqCt))
canTyEqCanLHS2 ev swapped lhs1 ps_xi1 lhs2 ps_xi2 mkco
  | lhs1 `eqCanTyEqLHS` lhs2
  = canTyEqReflexive ev lhs1_ty

  | TyVarLHS tv1 <- lhs1
  , TyVarLHS tv2 <- lhs2
  = do traceTcS "canTyEqLHS2 swapOver" (ppr tv1 $$ ppr tv2 $$ ppr swapped)
       if swapOverTyVars (isGiven ev) tv1 tv2
         then finish_with_swapping
         else finish_without_swapping
  where
    sym_mkco = mkSymMKiCo mkco
    lhs1_ty = canTyEqLHSType lhs1
    lhs2_ty = canTyEqLHSType lhs2

    finish_without_swapping = canTyEqCanLHSFinish ev swapped lhs1 (ps_xi2 `mkCastTyMCo` mkco)

    finish_with_swapping = do
      let lhs1_redn = mkGReflRightMRednTy lhs1_ty sym_mkco
          lhs2_redn = mkGReflLeftMRednTy lhs2_ty mkco
      new_ev <- rewriteTyEqEvidence emptyTyRewriterSet ev swapped lhs1_redn lhs2_redn
      canTyEqCanLHSFinish new_ev IsSwapped lhs2 (ps_xi1 `mkCastTyMCo` sym_mkco)

canTyEqCanLHSFinish
  :: CtTyEvidence
  -> SwapFlag
  -> CanTyEqLHS
  -> AnyType
  -> TcS (StopOrContinueTy (Either IrredTyCt TyEqCt))
canTyEqCanLHSFinish ev swapped lhs rhs = do
  traceTcS "canTyEqCanLHSFinish"
    $ vcat [ text "ev:" <+> ppr ev
           , text "swapped:" <+> ppr swapped
           , text "lhs:" <+> ppr lhs
           , text "rhs:" <+> ppr rhs ]

  massert (canTyEqLHSKind lhs `eqMonoKind` typeMonoKind rhs)

  canTyEqCanLHSFinish_try_unification ev swapped lhs rhs

canTyEqCanLHSFinish_try_unification
  :: CtTyEvidence
  -> SwapFlag
  -> CanTyEqLHS
  -> AnyType
  -> TcS (StopOrContinueTy (Either IrredTyCt TyEqCt))
canTyEqCanLHSFinish_try_unification ev swapped lhs rhs
  | isWanted ev
  , TyVarLHS tv <- lhs
  = do given_eq_lvl <- getInnermostGivenTyEqLevel
       case toTcTyVar_maybe tv of
         Just tv
           | touchabilityAndShapeTestType given_eq_lvl tv rhs
             -> do check_result <- checkTouchableTyVarEq ev tv rhs
                   case check_result of
                     PuFail reason
                       | reason `ctkerHasOnlyProblems` do_not_prevent_rewriting
                         -> canTyEqCanLHSFinish_no_unification ev swapped lhs rhs
                       | otherwise
                         -> tryIrredTyInstead reason ev swapped lhs rhs
                     PuOK _ rhs_redn ->
                       do let tv_ty = mkTyVarTy $ toAnyTyVar tv
                          new_ev <- if isReflTyCo (reductionTypeCoercion rhs_redn)
                                    then return ev
                                    else rewriteTyEqEvidence emptyTyRewriterSet ev swapped
                                         (mkReflRednTy tv_ty) rhs_redn
                          let final_rhs = reductionReducedType rhs_redn
                          traceTcS " Sneaky unification:"
                            $ vcat [ text "Unifies:" <+> ppr tv <+> text ":=" <+> ppr final_rhs
                                   , text "Coercion:" <+> pprEq tv_ty final_rhs
                                   , text "Left Kind is:" <+> ppr (typeKind tv_ty)
                                   , text "Right Kind is:" <+> ppr (typeKind final_rhs) ]

                          unifyTyVar tv final_rhs

                          setTyCoBindIfWanted new_ev $ mkReflTyCo final_rhs

                          kickOutAfterTyUnification [tv]

                          return (Stop new_ev (text "Solve by unification"))

         _ -> canTyEqCanLHSFinish_no_unification ev swapped lhs rhs
  | otherwise
  = canTyEqCanLHSFinish_no_unification ev swapped lhs rhs
  where
    do_not_prevent_rewriting = ctkeProblem ctkeSkolemEscape S.<> ctkeProblem ctkeConcrete

canTyEqCanLHSFinish_no_unification
  :: CtTyEvidence
  -> SwapFlag
  -> CanTyEqLHS
  -> AnyType
  -> TcS (StopOrContinueTy (Either IrredTyCt TyEqCt))
canTyEqCanLHSFinish_no_unification ev swapped lhs rhs = do
  check_result <- checkTypeEq ev lhs rhs

  let lhs_ty = canTyEqLHSType lhs
  case check_result of
    PuFail reason -> tryIrredTyInstead reason ev swapped lhs rhs
    PuOK _ rhs_redn -> do
      new_ev <- rewriteTyEqEvidence emptyTyRewriterSet ev swapped
                (mkReflRednTy lhs_ty) rhs_redn
      continueWith $ Right $ TyEqCt { teq_ev = new_ev
                                    , teq_lhs = lhs
                                    , teq_rhs = reductionReducedType rhs_redn }

{- *********************************************************************
*                                                                      *
*           canonicaliseKiCoercion
*                                                                      *
********************************************************************* -}

canonicalizeKiCoercion
  :: CtKiEvidence
  -> KiPredCon
  -> AnyMonoKind
  -> AnyMonoKind
  -> KiSolverStage (Either IrredKiCt KiCoCt)
canonicalizeKiCoercion ev kc ki1 ki2 = Stage $ do
  traceTcS "canonicalizeKiCoercion"
    $ vcat [ ppr ev, ppr kc, ppr ki1, ppr ki2 ]
  rdr_env <- getGlobalRdrEnvTcS
  can_ki_co_nc False rdr_env ev kc ki1 ki2

can_ki_co_nc
  :: Bool
  -> GlobalRdrEnv
  -> CtKiEvidence
  -> KiPredCon
  -> AnyMonoKind
  -> AnyMonoKind
  -> TcS (StopOrContinueKi (Either IrredKiCt KiCoCt))

can_ki_co_nc _ _ ev kc ki1@(BIKi kc1) (BIKi kc2) 
  | kc1 == kc2
  , kc == EQKi
  = canKiCoReflexive ev ki1
  | kc1 == kc2
  , kc == LTEQKi
  = canKiCoLiftReflexive ev ki1
  | kc1 < kc2
  , kc == LTEQKi
  = canKiCoLiftLT ev kc1 kc2
  | kc1 < kc2
  , kc == LTKi
  = canKiCoLT ev kc1 kc2

can_ki_co_nc True _ ev kc ki1 ki2
  | ki1 `tcEqMonoKind` ki2
  , kc == EQKi
  = canKiCoReflexive ev ki1
  | ki1 `tcEqMonoKind` ki2
  , kc == LTEQKi
  = canKiCoLiftReflexive ev ki1

can_ki_co_nc True _ ev kc ki1 ki2
  | ki1 `tcLTEQMonoKind` ki2
  , kc == LTEQKi
  = canKiCoBILTEQ ev ki1 ki2

----------------------
-- Otherwise try to decompose
----------------------

can_ki_co_nc _ _ ev kc (FunKi f1 ki1a ki1b) (FunKi f2 ki2a ki2b)
  | f1 == f2
  = canDecomposableFunKi ev kc f1 (ki1a, ki1b) (ki2a, ki2b)

can_ki_co_nc _ _ ev kc (KiPredApp kc1 ka1 kb1) (KiPredApp kc2 ka2 kb2)
  = panic "canKiConApp ev kc kc1 kis1 kc2 kis2" -- this souldn't really happen (need to refactor kind to prevent this)

------------------
-- Can't decompose
------------------

can_ki_co_nc False rdr_env ev kc ps_ki1 ps_ki2 = do
  (redn1@(KiReduction _ xi1), rewriters1) <- rewriteKi ev ps_ki1
  (redn2@(KiReduction _ xi2), rewriters2) <- rewriteKi ev ps_ki2
  new_ev <- rewriteKiCoEvidence (rewriters1 S.<> rewriters2) ev NotSwapped redn1 redn2
  traceTcS "can_ki_co_nc: go round again" (ppr new_ev $$ ppr xi1 $$ ppr xi2)
  can_ki_co_nc True rdr_env new_ev kc xi1 xi2

can_ki_co_nc True _ ev kc ki1 ki2
  | Just can_co_lhs1 <- canKiCoLHS_maybe ki1
  = do traceTcS "can_ki_co1" (ppr ki1 $$ ppr ki2)
       canKiCoCanLHSHomo ev NotSwapped kc can_co_lhs1 ki1 ki2 ki2

  | Just can_co_lhs2 <- canKiCoLHS_maybe ki2
  = do traceTcS "can_ki_co2" (ppr ki1 $$ ppr ki2)
       canKiCoCanLHSHomo ev IsSwapped kc can_co_lhs2 ki2 ki1 ki1

------------------
-- Failed
------------------

can_ki_co_nc True _ ev kc ps_ki1 ps_ki2 = do
  traceTcS "can_ki_co_nc catch-all case" (ppr kc $$ ppr ps_ki1 $$ ppr ps_ki2)
  finishCanWithIrredKi ShapeMismatchReason ev

canDecomposableFunKi
  :: CtKiEvidence
  -> KiPredCon
  -> FunKiFlag
  -> (AnyMonoKind, AnyMonoKind)
  -> (AnyMonoKind, AnyMonoKind)
  -> TcS (StopOrContinueKi a)
canDecomposableFunKi ev kc f f1@(a1, r1) f2@(a2, r2) = do
  massertPpr (kc == EQKi)
    $ vcat [ text "canDecomposableFunKi has non-equality constraint"
           , ppr ev, ppr kc, ppr f1, ppr f2 ]
  traceTcS "canDecomposableFunKi"
    $ ppr ev $$ ppr f1 $$ ppr f2
  case ev of
    CtKiWanted { ctkev_dest = dest } -> do
      (co, _, _) <- wrapKiUnifierTcS ev $ \uenv -> do
        arg <- uKind uenv EQKi a1 a2
        res <- uKind uenv EQKi r1 r2
        return $ mkFunKiCo f arg res
      setWantedKiCo dest co
    CtKiGiven { ctkev_covar = covar } -> pprPanic "canDecomposableFunKi"
                                     $ vcat [ ppr ev, ppr f1, ppr f2 ]
  stopWith ev "Decomposed FunKi"

canKiCoHardFailure
  :: CtKiEvidence
  -> AnyMonoKind
  -> AnyMonoKind
  -> TcS (StopOrContinueKi (Either IrredKiCt a))
canKiCoHardFailure ev ki1 ki2 = do
  traceTcS "canKiCoHardFailure" (ppr ki1 $$ ppr ki2)
  (redn1, rewriters1) <- rewriteKiForErrors ev ki1
  (redn2, rewriters2) <- rewriteKiForErrors ev ki2
  new_ev <- rewriteKiCoEvidence (rewriters1 S.<> rewriters2) ev NotSwapped redn1 redn2
  finishCanWithIrredKi ShapeMismatchReason new_ev

canKiCoCanLHSHomo
  :: CtKiEvidence
  -> SwapFlag
  -> KiPredCon
  -> CanKiCoLHS
  -> AnyMonoKind
  -> AnyMonoKind
  -> AnyMonoKind
  -> TcS (StopOrContinueKi (Either IrredKiCt KiCoCt))
canKiCoCanLHSHomo ev swapped kc lhs1 ps_xi1 xi2 ps_xi2
  | Just lhs2 <- canKiCoLHS_maybe xi2
  = canKiCoCanLHS2 ev swapped lhs1 ps_xi1 lhs2 ps_xi2
  | otherwise
  = canKiCoCanLHSFinish ev swapped lhs1 ps_xi2

canKiCoCanLHS2
  :: CtKiEvidence
  -> SwapFlag
  -> CanKiCoLHS
  -> AnyMonoKind
  -> CanKiCoLHS
  -> AnyMonoKind
  -> TcS (StopOrContinueKi (Either IrredKiCt KiCoCt))
canKiCoCanLHS2 ev swapped lhs1 ps_xi1 lhs2 ps_xi2
  | lhs1 `eqCanKiCoLHS` lhs2
  = canKiCoReflexive ev lhs1_ki
  | KiVarLHS kv1 <- lhs1
  , KiVarLHS kv2 <- lhs2
  = do traceTcS "canEqLHS2 swapOver" (ppr kv1 $$ ppr kv2 $$ ppr swapped)
       if swapOverKiVars (isGiven ev) kv1 kv2
         then finish_with_swapping
         else finish_without_swapping

  where
    lhs1_ki = canKiCoLHSKind lhs1
    lhs2_ki = canKiCoLHSKind lhs2

    finish_without_swapping = canKiCoCanLHSFinish ev swapped lhs1 ps_xi2

    finish_with_swapping = do
      new_ev <- rewriteKiCoEvidence
                emptyKiRewriterSet ev swapped (mkReflRednKi lhs1_ki) (mkReflRednKi lhs2_ki)
      canKiCoCanLHSFinish new_ev IsSwapped lhs2 ps_xi1

canKiCoCanLHSFinish
  :: CtKiEvidence
  -> SwapFlag
  -> CanKiCoLHS
  -> AnyMonoKind
  -> TcS (StopOrContinueKi (Either IrredKiCt KiCoCt))
canKiCoCanLHSFinish ev swapped lhs rhs = do
  traceTcS "canKiCoCanLHSFinish"
    $ vcat [ text "ev:" <+> ppr ev
           , text "swapped:" <+> ppr swapped
           , text "lhs:" <+> ppr lhs
           , text "rhs:" <+> ppr rhs ]

  canKiCoCanLHSFinish_try_unification ev swapped lhs rhs

canKiCoCanLHSFinish_try_unification
  :: CtKiEvidence
  -> SwapFlag
  -> CanKiCoLHS
  -> AnyMonoKind
  -> TcS (StopOrContinueKi (Either IrredKiCt KiCoCt))
canKiCoCanLHSFinish_try_unification ev swapped lhs rhs
  | isWanted ev
  , KiVarLHS kv <- lhs
  = do given_eq_lvl <- getInnermostGivenKiCoLevel
       case toTcKiVar_maybe kv of
         Just kv
           | touchabilityAndShapeTestKind given_eq_lvl kv rhs
             -> do check_result <- checkTouchableKiVarEq ev kv rhs
                   case check_result of
                     PuFail reason
                       | reason `ctkerHasOnlyProblems` do_not_prevent_rewriting
                         -> canKiCoCanLHSFinish_no_unification ev swapped lhs rhs
                       | otherwise
                         -> tryIrredKiInstead reason ev swapped lhs rhs
                     PuOK _ rhs_redn ->
                       do let kv_ki = mkKiVarKi $ toAnyKiVar kv
                          new_ev <- if isReflKiCo (reductionKindCoercion rhs_redn)
                                    then return ev
                                    else rewriteKiCoEvidence emptyKiRewriterSet
                                         ev swapped (mkReflRednKi kv_ki) rhs_redn
                          let final_rhs = reductionReducedKind rhs_redn
                   
                          traceTcS "Sneaky unification:"
                            $ text "Unifies:" <+> ppr kv <+> text ":=" <+> ppr final_rhs
                   
                          unifyKiVar kv final_rhs

                          setKiCoBindIfWanted new_ev $ case ctKiEvRel new_ev of
                            EQKi -> mkReflKiCo final_rhs
                            LTEQKi -> LiftEq $ mkReflKiCo final_rhs
                            _ -> panic "canKiCoCanLHSFinish_try_unification unreachable"

                          kickOutAfterKiUnification [kv]
                   
                          return $ Stop new_ev (text "Solved by unification")
                          
         _ -> canKiCoCanLHSFinish_no_unification ev swapped lhs rhs
  | otherwise
  = canKiCoCanLHSFinish_no_unification ev swapped lhs rhs
  where
    do_not_prevent_rewriting = ctkeProblem ctkeSkolemEscape S.<> ctkeProblem ctkeConcrete

canKiCoCanLHSFinish_no_unification
  :: CtKiEvidence
  -> SwapFlag
  -> CanKiCoLHS
  -> AnyMonoKind
  -> TcS (StopOrContinueKi (Either IrredKiCt KiCoCt))
canKiCoCanLHSFinish_no_unification ev swapped lhs rhs = do
  check_result <- checkKindEq ev lhs rhs
  case check_result of
    PuFail reason -> tryIrredKiInstead reason ev swapped lhs rhs
    PuOK _ rhs_redn -> do
      let lhs_ki = canKiCoLHSKind lhs
      new_ev <- rewriteKiCoEvidence emptyKiRewriterSet ev swapped (mkReflRednKi lhs_ki) rhs_redn
      continueWith $ Right $ KiCoCt { kc_ev = new_ev
                                    , kc_lhs = lhs
                                    , kc_rhs = reductionReducedKind rhs_redn
                                    , kc_pred = panic "kc_rel" }

tryIrredTyInstead
  :: CheckTyKiEqResult
  -> CtTyEvidence
  -> SwapFlag
  -> CanTyEqLHS
  -> AnyType
  -> TcS (StopOrContinueTy (Either IrredTyCt a))
tryIrredTyInstead reason ev swapped lhs rhs = do
  traceTcS "cantMakeCanonical" (ppr reason $$ ppr lhs $$ ppr rhs)
  new_ev <- rewriteTyEqEvidence emptyTyRewriterSet ev swapped
            (mkReflRednTy (canTyEqLHSType lhs))
            (mkReflRednTy rhs)
  finishCanWithIrredTy (NonCanonicalReason reason) new_ev

tryIrredKiInstead
  :: CheckTyKiEqResult
  -> CtKiEvidence
  -> SwapFlag
  -> CanKiCoLHS
  -> AnyMonoKind
  -> TcS (StopOrContinueKi (Either IrredKiCt a))
tryIrredKiInstead reason ev swapped lhs rhs = do
  traceTcS "cantMakeCaconical" (ppr reason $$ ppr lhs $$ ppr rhs)
  new_ev <- rewriteKiCoEvidence
            emptyKiRewriterSet ev swapped (mkReflRednKi $ canKiCoLHSKind lhs) (mkReflRednKi rhs)
  finishCanWithIrredKi (NonCanonicalReason reason) new_ev

finishCanWithIrredKi
  :: CtIrredReason -> CtKiEvidence -> TcS (StopOrContinueKi (Either IrredKiCt a))
finishCanWithIrredKi reason ev = do
  when (isInsolubleReason reason) tryEarlyAbortTcS
  continueWith $ Left $ IrredKiCt { ikr_ev = ev, ikr_reason = reason }

finishCanWithIrredTy
  :: CtIrredReason -> CtTyEvidence -> TcS (StopOrContinueTy (Either IrredTyCt a))
finishCanWithIrredTy reason ev = do
  when (isInsolubleReason reason) tryEarlyAbortTcS
  continueWith $ Left $ IrredTyCt { itr_ev = ev, itr_reason = reason }

canTyEqReflexive :: CtTyEvidence -> AnyType -> TcS (StopOrContinueTy a)
canTyEqReflexive ev ty = do
  setTyCoBindIfWanted ev $ mkReflTyCo ty
  stopWith ev "Solved by reflexivity"

canKiCoReflexive :: CtKiEvidence -> AnyMonoKind -> TcS (StopOrContinueKi a)
canKiCoReflexive ev ki = do
  setKiCoBindIfWanted ev $ mkReflKiCo ki
  stopWith ev "Solved by reflexivity"

canKiCoLiftReflexive :: CtKiEvidence -> AnyMonoKind -> TcS (StopOrContinueKi a)
canKiCoLiftReflexive ev ki = do
  setKiCoBindIfWanted ev $ LiftEq $ mkReflKiCo ki
  stopWith ev "Solved by lifting reflexivity"

canKiCoLT :: CtKiEvidence -> BuiltInKi -> BuiltInKi -> TcS (StopOrContinueKi a)
canKiCoLT ev kc1 kc2 = do
  let co = case (kc1, kc2) of
             (UKd, AKd) -> BI_U_A
             (AKd, LKd) -> BI_A_L
             (UKd, LKd) -> TransCo BI_U_A BI_A_L
             _ -> pprPanic "canKiCoLT" (ppr ev $$ ppr kc1 $$ ppr kc2)
  setKiCoBindIfWanted ev $ co
  stopWith ev "Solved by built-in"

canKiCoLiftLT :: CtKiEvidence -> BuiltInKi -> BuiltInKi -> TcS (StopOrContinueKi a)
canKiCoLiftLT ev kc1 kc2 = do
  let co = case (kc1, kc2) of
             (UKd, AKd) -> BI_U_A
             (AKd, LKd) -> BI_A_L
             (UKd, LKd) -> TransCo BI_U_A BI_A_L
             _ -> pprPanic "canKiCoLT" (ppr ev $$ ppr kc1 $$ ppr kc2)
  setKiCoBindIfWanted ev $ LiftLT co
  stopWith ev "Solved by lifting built-in"
 
canKiCoBILTEQ :: CtKiEvidence -> AnyMonoKind -> AnyMonoKind -> TcS (StopOrContinueKi a)
canKiCoBILTEQ ev k1 k2 = do
  let co = case (k1, k2) of
             (BIKi UKd, _) -> BI_U_LTEQ k2
             (_, BIKi LKd) -> BI_LTEQ_L k1
             _ -> pprPanic "canKiCoBILTEQ" (ppr ev $$ ppr k1 $$ ppr k2)
  setKiCoBindIfWanted ev co
  stopWith ev "Solved by built-in"

{- *******************************************************************
*                                                                    *
                   Rewriting evidence
*                                                                    *
******************************************************************* -}

rewriteTyEqEvidence
  :: TyRewriterSet
  -> CtTyEvidence
  -> SwapFlag
  -> TyReduction
  -> TyReduction
  -> TcS CtTyEvidence
rewriteTyEqEvidence new_rewriters old_ev swapped (TyReduction lhs_co nlhs) (TyReduction rhs_co nrhs)
  | NotSwapped <- swapped
  , isReflTyCo lhs_co
  , isReflTyCo rhs_co
  = return $ setCtEvPredType old_ev new_pred
  | CtTyGiven { cttev_covar = old_covar } <- old_ev
  = panic "rewriteTyEqEvidence"
  | CtTyWanted { cttev_dest = dest, cttev_rewriters = rewriters } <- old_ev
  , let rewriters' = rewriters S.<> new_rewriters
  = do (new_ev, hole_co) <- newWantedTyCo loc rewriters' nlhs nrhs
       let co = maybeSymTyCo swapped $
                lhs_co `mkTyTransCo` hole_co `mkTyTransCo` mkSymTyCo rhs_co
       setWantedTyCo dest co
       traceTcS  "rewriteTyEqEvidence"
         $ vcat [ ppr old_ev
                , ppr nlhs
                , ppr nrhs
                , ppr co
                , ppr new_rewriters ]
       return new_ev
  where
    new_pred = mkTyEqPred nlhs nrhs
    loc = ctEvLoc old_ev

rewriteKiCoEvidence
  :: KiRewriterSet
  -> CtKiEvidence
  -> SwapFlag
  -> KiReduction
  -> KiReduction
  -> TcS CtKiEvidence
rewriteKiCoEvidence new_rewriters old_ev swapped (KiReduction lhs_co nlhs) (KiReduction rhs_co nrhs)
  | NotSwapped <- swapped
  , isReflKiCo lhs_co
  , isReflKiCo rhs_co
  = return $ setCtEvPredKind old_ev new_pred
  | CtKiGiven { ctkev_covar = old_covar } <- old_ev
  = panic "rewriteKiCoEvidence"
  | CtKiWanted { ctkev_dest = dest, ctkev_rewriters = rewriters } <- old_ev
  , let rewriters' = rewriters S.<> new_rewriters
  = do (new_ev, hole_co) <- newWantedKiCo loc rewriters' kc nlhs nrhs
       let co = maybeSymKiCo swapped $
                lhs_co `mkTransKiCo` hole_co `mkTransKiCo` mkSymKiCo rhs_co
       setWantedKiCo dest co
       traceTcS "rewriteKiCoEvidence"
         $ vcat [ ppr old_ev, ppr swapped, ppr nlhs, ppr nrhs, ppr hole_co
                , ppr co, ppr new_rewriters ]
       return new_ev
  where
    new_pred = mkKiCoPred kc nlhs nrhs
    loc = ctEvLoc old_ev
    kc = fstOf3 $ getPredKis $ ctKiEvPred old_ev

{- *******************************************************************
*                                                                    *
                   tryInertEqs
*                                                                    *
******************************************************************* -}

tryInertTyEqs :: TyEqCt -> TySolverStage ()
tryInertTyEqs work_item@(TyEqCt { teq_ev = ev }) = Stage $ do
  inerts <- getInertTyCans
  case tyInertsCanDischarge inerts work_item of
    Just (ev_i, swapped) -> do
      setTyCoBindIfWanted ev (maybeSymTyCo swapped (ctEvTyCoercion ev_i))
      stopWith ev "Solved from inert"
    Nothing -> continueWith ()

tyInertsCanDischarge :: InertTyCans -> TyEqCt -> Maybe (CtTyEvidence, SwapFlag)
tyInertsCanDischarge inerts (TyEqCt { teq_lhs = lhs_w, teq_rhs = rhs_w, teq_ev = ev_w })
  | (ev_i : _) <- [ ev_i | TyEqCt { teq_ev = ev_i, teq_rhs = rhs_i } <- findTyEq inerts lhs_w
                         , rhs_i `tcEqType` rhs_w
                         , inert_beats_wanted ev_i ]
  = Just (ev_i, NotSwapped)

  | Just rhs_lhs <- canTyEqLHS_maybe rhs_w
  , (ev_i : _) <- [ ev_i | TyEqCt { teq_ev = ev_i, teq_rhs = rhs_i } <- findTyEq inerts rhs_lhs
                         , rhs_i `tcEqType` canTyEqLHSType lhs_w
                         , inert_beats_wanted ev_i ]
  = Just (ev_i, IsSwapped)

  | otherwise = Nothing

  where
    loc_w = ctEvLoc ev_w
    f_w = ctEvFlavor ev_w

    inert_beats_wanted ev_i
      = f_i `eqCanRewriteF` f_w
      && not ((loc_w `strictly_more_visible` ctEvLoc ev_i)
              && (f_w `eqCanRewriteF` f_i))
      where
        f_i = ctEvFlavor ev_i

    strictly_more_visible loc1 loc2
      = not (isVisibleOrigin (ctLocOrigin loc2))
        && isVisibleOrigin (ctLocOrigin loc1)
    

tryInertKiCos :: KiCoCt -> KiSolverStage ()
tryInertKiCos work_item@(KiCoCt { kc_ev = ev }) = Stage $ do
  inerts <- getInertKiCans
  case kiInertsCanDischarge inerts work_item of
    Just (ev_i, swapped) -> do
      setKiCoBindIfWanted ev (maybeSymKiCo swapped (ctEvKiCoercion ev_i))
      stopWith ev "Solved from inert"
    Nothing -> continueWith ()

kiInertsCanDischarge :: InertKiCans -> KiCoCt -> Maybe (CtKiEvidence, SwapFlag)
kiInertsCanDischarge inerts (KiCoCt { kc_lhs = lhs_w, kc_rhs = rhs_w, kc_ev = ev_w })
  | (ev_i : _) <- [ ev_i | KiCoCt { kc_ev = ev_i, kc_rhs = rhs_i }
                           <- findKiCo inerts lhs_w
                         , rhs_i `tcEqMonoKind` rhs_w
                         , inert_beats_wanted ev_i ]
  = Just (ev_i, NotSwapped)

  | Just rhs_lhs <- canKiCoLHS_maybe rhs_w
  , (ev_i : _) <- [ ev_i | KiCoCt { kc_ev = ev_i, kc_rhs = rhs_i }
                           <- findKiCo inerts rhs_lhs
                         , rhs_i `tcEqMonoKind` canKiCoLHSKind lhs_w
                         , inert_beats_wanted ev_i ]
  = Just (ev_i, IsSwapped)
  where
    loc_w = ctEvLoc ev_w
    f_w = ctEvFlavor ev_w

    inert_beats_wanted ev_i
      = f_i `eqCanRewriteF` f_w
        && not ((loc_w `strictly_more_visible` ctEvLoc ev_i)
                && (f_w `eqCanRewriteF` f_i))
      where
        f_i = ctEvFlavor ev_i

    strictly_more_visible loc1 loc2
      = not (isVisibleOrigin (ctLocOrigin loc2))
        && isVisibleOrigin (ctLocOrigin loc1)

kiInertsCanDischarge _ _ = Nothing

{-********************************************************************
*                                                                    *
          Final wrap-up for equalities
*                                                                    *
********************************************************************-}

tryQCsIrredTyEqCt :: IrredTyCt -> TySolverStage ()
tryQCsIrredTyEqCt irred@(IrredTyCt { itr_ev = ev })
  | TyEqPred t1 t2 <- classifyPredType (ctTyEvPred ev)
  = lookup_ty_eq_in_qcis (CIrredCanTy irred) t1 t2
  | otherwise
  = pprPanic "solverIrredEquality" (ppr ev)

tryQCsTyEqCt :: TyEqCt -> TySolverStage ()
tryQCsTyEqCt work_item@(TyEqCt { teq_lhs = lhs, teq_rhs = rhs })
  = lookup_ty_eq_in_qcis (CTyEqCan work_item) (canTyEqLHSType lhs) rhs

lookup_ty_eq_in_qcis :: TyCt -> AnyType -> AnyType -> TySolverStage ()
lookup_ty_eq_in_qcis _ _ _ = Stage $ continueWith ()

tryQCsIrredKiCoCt :: IrredKiCt -> KiSolverStage ()
tryQCsIrredKiCoCt irred@(IrredKiCt { ikr_ev = ev })
  | KiCoPred kc k1 k2 <- classifyPredKind (ctKiEvPred ev)
  = lookup_ki_co_in_qcis (CIrredCanKi irred) k1 k2
  | otherwise
  = pprPanic "solveIrredEquality" (ppr ev)

tryQCsKiCoCt :: KiCoCt -> KiSolverStage ()
tryQCsKiCoCt work_item@(KiCoCt { kc_lhs = lhs, kc_rhs = rhs })
  = lookup_ki_co_in_qcis (CKiCoCan work_item) (canKiCoLHSKind lhs) rhs

lookup_ki_co_in_qcis :: KiCt -> AnyMonoKind -> AnyMonoKind -> KiSolverStage ()
lookup_ki_co_in_qcis work_ct lhs rhs = Stage $ do
  continueWith ()
