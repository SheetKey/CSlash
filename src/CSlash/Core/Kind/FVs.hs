module CSlash.Core.Kind.FVs where

import {-# SOURCE #-} CSlash.Core.Type.FVs (deep_ty)

import Data.Monoid as DM ( Endo(..), Any(..) )
import CSlash.Core.Kind
import CSlash.Core.TyCon

import CSlash.Types.Var
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Set

import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Utils.Misc
import CSlash.Utils.FV
import CSlash.Utils.Panic

{- *********************************************************************
*                                                                      *
          Endo for free variables
*                                                                      *
********************************************************************* -}

runKiVars :: Endo KiVarSet -> KiVarSet
{-# INLINE runKiVars #-}
runKiVars f = appEndo f emptyVarSet

{- *********************************************************************
*                                                                      *
          Deep free variables
*                                                                      *
********************************************************************* -}

kiVarsOfKind :: Kind -> KiVarSet
kiVarsOfKind ki = runKiVars (deep_ki ki)

kiVarsOfMonoKind :: MonoKind -> KiVarSet
kiVarsOfMonoKind ki = runKiVars (deep_ki (Mono ki))

kiVarsOfKinds :: [Kind] -> KiVarSet
kiVarsOfKinds kis = runKiVars (deep_kis kis)

deep_ki :: Kind -> Endo KiVarSet
deep_kis :: [Kind] -> Endo KiVarSet
(deep_ki, deep_kis) = foldKind deepKvFolder emptyVarSet

deepKvFolder :: KindFolder KiVarSet (Endo KiVarSet)
deepKvFolder = KindFolder { kf_view = noKindView
                          , kf_kivar = do_kv
                          , kf_kibinder = do_bndr }
  where
    do_kv is v = Endo do_it
      where
        do_it acc | v `elemVarSet` is = acc
                  | v `elemVarSet` acc = acc
                  | otherwise = acc `extendVarSet` v

    do_bndr is kv = extendVarSet is kv

{- *********************************************************************
*                                                                      *
          Shallow free variables
*                                                                      *
********************************************************************* -}

shallowKiVarsOfMonoKind :: MonoKind -> KiVarSet
shallowKiVarsOfMonoKind ki = runKiVars (shallow_ki (Mono ki))

shallowKiVarsOfKind :: Kind -> KiVarSet
shallowKiVarsOfKind ki = runKiVars (shallow_ki ki)

shallowKiVarsOfKinds :: [Kind] -> KiVarSet
shallowKiVarsOfKinds kis = runKiVars (shallow_kis kis)

shallowKiVarsOfMonoKinds :: [MonoKind] -> KiVarSet
shallowKiVarsOfMonoKinds kis = runKiVars (shallow_kis (Mono <$> kis))

shallowKiVarsOfKiVarEnv :: KiVarEnv Kind -> KiVarSet
shallowKiVarsOfKiVarEnv kis = shallowKiVarsOfKinds (nonDetEltsUFM kis)

shallowKiVarsOfMonoKiVarEnv :: KiVarEnv MonoKind -> KiVarSet
shallowKiVarsOfMonoKiVarEnv kis = shallowKiVarsOfMonoKinds (nonDetEltsUFM kis)

shallow_ki :: Kind -> Endo KiVarSet
shallow_kis :: [Kind] -> Endo KiVarSet

(shallow_ki, shallow_kis) = foldKind shallowKvFolder emptyVarSet

shallowKvFolder :: KindFolder KiVarSet (Endo KiVarSet)
shallowKvFolder = KindFolder { kf_view = noKindView
                             , kf_kivar = do_kv
                             , kf_kibinder = do_bndr
                             }
  where
    do_kv is v = Endo do_it
      where
        do_it acc | v `elemVarSet` is = acc
                  | v `elemVarSet` acc = acc
                  | otherwise = acc `extendVarSet` v
    do_bndr is kv = extendVarSet is kv

{- *********************************************************************
*                                                                      *
          Deep Free ki/coercion variables
*                                                                      *
********************************************************************* -}

runKiCoVars :: Endo KiCoVarSet -> KiCoVarSet
runKiCoVars f = appEndo f emptyVarSet
{-# INLINE runKiCoVars #-}

kiCoVarsOfKiCo :: KindCoercion -> KiCoVarSet
kiCoVarsOfKiCo co = runKiCoVars (deep_cv_co co)

kiCoVarsOfMonoKind :: MonoKind -> KiCoVarSet
kiCoVarsOfMonoKind mki = runKiCoVars (deep_cv_ki mki)

deep_cv_ki :: MonoKind -> Endo KiCoVarSet
deep_cv_kis :: [MonoKind] -> Endo KiCoVarSet
deep_cv_co :: KindCoercion -> Endo KiCoVarSet
deep_cv_cos :: [KindCoercion] -> Endo KiCoVarSet
(deep_cv_ki, deep_cv_kis, deep_cv_co, deep_cv_cos) = foldMonoKiCo deepKiCoVarFolder emptyVarSet

deepKiCoVarFolder :: MonoKiCoFolder KiCoVarSet (Endo KiCoVarSet)
deepKiCoVarFolder = MKiCoFolder { kcf_kivar = do_kcv
                                , kcf_covar = do_kcv
                                , kcf_hole = do_hole }
  where
    do_kcv is v = Endo do_it
      where
        do_it acc | v `elemVarSet` is = acc
                  | v `elemVarSet` acc = acc
                  | isTyVar v = appEndo (deep_ty (varType v)) $
                                acc `extendVarSet` v
                  | otherwise = acc `extendVarSet` v
    do_hole is hole = do_kcv is (coHoleCoVar hole)

{- *********************************************************************
*                                                                      *
          Free coercion variables
*                                                                      *
********************************************************************* -}

coVarsOfKiCo :: KindCoercion -> KiCoVarSet
coVarsOfKiCo co = runKiCoVars (deep_cv_only_co co)

deep_cv_only_co :: KindCoercion -> Endo KiCoVarSet
(_, _, deep_cv_only_co, _) = foldMonoKiCo deepKiCoVarOnlyFolder emptyVarSet

deepKiCoVarOnlyFolder :: MonoKiCoFolder KiCoVarSet (Endo KiCoVarSet)
deepKiCoVarOnlyFolder = MKiCoFolder { kcf_kivar = do_kivar
                                    , kcf_covar = do_covar
                                    , kcf_hole = do_hole }
  where
    do_kivar _ _ = mempty

    do_covar is v = Endo do_it
      where
        do_it acc | v `elemVarSet` is = acc
                  | v `elemVarSet` acc = acc
                  | otherwise = acc `extendVarSet` v

    do_hole is hole = do_covar is (coHoleCoVar hole)

{- *********************************************************************
*                                                                      *
          The FV versions return deterministic results
*                                                                      *
********************************************************************* -}

kiVarsOfKindDSet :: Kind -> DKiVarSet 
kiVarsOfKindDSet ki = fvDVarSet $ kiFVsOfKind ki

kiVarsOfKindList :: Kind -> [KindVar]
kiVarsOfKindList ki = fvVarList $ kiFVsOfKind ki

kiCoVarsOfMonoKindList :: MonoKind -> [KiCoVar]
kiCoVarsOfMonoKindList ki = fvVarList $ kiFVsOfMonoKind ki

kiCoVarsOfMonoKindsList :: [MonoKind] -> [KiCoVar]
kiCoVarsOfMonoKindsList kis = fvVarList $ kiFVsOfMonoKinds kis

kiFVsOfKind :: Kind -> FV
kiFVsOfKind (Mono ki) f bound_vars acc = kiFVsOfMonoKind ki f bound_vars acc
kiFVsOfKind (ForAllKi kv ki) f bound_vars acc
  = kiFVsVarBndr kv (kiFVsOfKind ki) f bound_vars acc

kiVarsOfMonoKindDSet :: MonoKind -> DKiVarSet 
kiVarsOfMonoKindDSet ki = fvDVarSet $ kiFVsOfMonoKind ki

kiVarsOfMonoKindList :: MonoKind -> [KindVar]
kiVarsOfMonoKindList ki = fvVarList $ kiFVsOfMonoKind ki

kiFVsOfMonoKind :: MonoKind -> FV
kiFVsOfMonoKind (KiVarKi v) f bound_vars (acc_list, acc_set)
  | not (f v) = (acc_list, acc_set)
  | v `elemVarSet` bound_vars = (acc_list, acc_set)
  | v `elemVarSet` acc_set = (acc_list, acc_set)
  | otherwise = (v:acc_list, extendVarSet acc_set v)
kiFVsOfMonoKind (KiConApp _ kis) f bound_vars acc = kiFVsOfMonoKinds kis f bound_vars acc
kiFVsOfMonoKind (FunKi _ arg res) f bound_var acc
  = (kiFVsOfMonoKind arg `unionFV` kiFVsOfMonoKind res) f bound_var acc

kiFVsVarBndr :: KindVar -> FV -> FV
kiFVsVarBndr kv fvs = delFV kv fvs

kiFVsOfMonoKinds :: [MonoKind] -> FV
kiFVsOfMonoKinds (ki:kis) fv_cand in_scope acc
  = (kiFVsOfMonoKind ki `unionFV` kiFVsOfMonoKinds kis) fv_cand in_scope acc
kiFVsOfMonoKinds [] fv_cand in_scope acc = emptyFV fv_cand in_scope acc

{- *********************************************************************
*                                                                      *
                 Any free vars
*                                                                      *
********************************************************************* -}

{-# INLINE afvFolder #-}
afvFolder :: (KindVar -> Bool) -> KindFolder KiVarSet DM.Any
afvFolder check_fv = KindFolder { kf_view = noKindView
                                , kf_kivar = \is kv -> Any (not (kv `elemVarSet` is)
                                                            && check_fv kv)
                                , kf_kibinder = \is kv -> is `extendVarSet` kv }

anyFreeVarsOfKind :: (KindVar -> Bool) -> Kind -> Bool
anyFreeVarsOfKind check_fv ki = DM.getAny (f ki)
  where (f, _) = foldKind (afvFolder check_fv) emptyVarSet

anyFreeVarsOfMonoKind :: (KindVar -> Bool) -> MonoKind -> Bool
anyFreeVarsOfMonoKind check_fv ki = DM.getAny (f (Mono ki))
  where (f, _) = foldKind (afvFolder check_fv) emptyVarSet

noFreeVarsOfKind :: Kind -> Bool
noFreeVarsOfKind ki = not $ DM.getAny (f ki)
  where (f, _) = foldKind (afvFolder (const True)) emptyVarSet

noFreeVarsOfMonoKind :: MonoKind -> Bool
noFreeVarsOfMonoKind ki = not $ DM.getAny (f (Mono ki))
  where (f, _) = foldKind (afvFolder (const True)) emptyVarSet

{- *********************************************************************
*                                                                      *
                 scopedSort
*                                                                      *
********************************************************************* -}

scopedSort :: [KiCoVar] -> [KiCoVar]
scopedSort = go []
  where
    go acc [] = reverse acc
    go acc (kv:kvs) = go acc' kvs
      where
        acc' = insert kv acc

    insert kv [] = [kv]
    insert kv (a:as) = (kv:a:as)

kiCoVarsOfMonoKindsWellScoped :: [MonoKind] -> [KindVar]
kiCoVarsOfMonoKindsWellScoped = scopedSort . kiCoVarsOfMonoKindsList
