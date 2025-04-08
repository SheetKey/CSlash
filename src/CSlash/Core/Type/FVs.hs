module CSlash.Core.Type.FVs where

import {-# SOURCE #-} CSlash.Core.Type (coreView)

import Data.Monoid as DM ( Endo(..), Any(..) )
import CSlash.Core.Type.Rep
import CSlash.Core.Kind.FVs
import CSlash.Core.TyCon

import CSlash.Types.Var
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Set

import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Utils.Misc
import CSlash.Utils.FV
import CSlash.Utils.Panic
import CSlash.Utils.Outputable

{- **********************************************************************
*                                                                       *
                 Free variables of types and coercions
*                                                                       *
********************************************************************** -}

{- *********************************************************************
*                                                                      *
          Endo for free variables
*                                                                      *
********************************************************************* -}

runTyVars :: Endo TyVarSet -> TyVarSet
{-# INLINE runTyVars #-}
runTyVars f = appEndo f emptyVarSet

{- *********************************************************************
*                                                                      *
          Deep free variables
*                                                                      *
********************************************************************* -}

-- does not close over kinds
tyVarsOfType :: Type -> TyVarSet
tyVarsOfType ty = runTyVars (deep_ty ty)

tyVarsOfTypes :: [Type] -> TyVarSet
tyVarsOfTypes tys = runTyVars (deep_tys tys)

deep_ty :: Type -> Endo TyVarSet
deep_tys :: [Type] -> Endo TyVarSet
(deep_ty, deep_tys) = foldType deepTvFolder emptyVarSet

deepTvFolder :: TypeFolder TyVarSet (Endo TyVarSet)
deepTvFolder = TypeFolder { tf_view = noView
                          , tf_tyvar = do_tv
                          , tf_tybinder = do_bndr }
  where
    do_tv is v = Endo do_it
      where
        do_it acc | v `elemVarSet` is = acc
                  | v `elemVarSet` acc = acc
                  | otherwise = acc `extendVarSet` v
    do_bndr is tv _ = extendVarSet is tv

{- *********************************************************************
*                                                                      *
          Shallow free variables
*                                                                      *
********************************************************************* -}

shallowTyVarsOfType :: Type -> TyVarSet
shallowTyVarsOfType ty = runTyVars (shallow_ty ty)

shallowTyVarsOfTypes :: [Type] -> TyVarSet
shallowTyVarsOfTypes tys = runTyVars (shallow_tys tys)

shallowTyVarsOfTyVarEnv :: TyVarEnv Type -> TyVarSet
shallowTyVarsOfTyVarEnv tys = shallowTyVarsOfTypes (nonDetEltsUFM tys)

shallow_ty :: Type -> Endo TyVarSet
shallow_tys :: [Type] -> Endo TyVarSet

(shallow_ty, shallow_tys) = foldType shallowTvFolder emptyVarSet

shallowTvFolder :: TypeFolder TyVarSet (Endo TyVarSet)
shallowTvFolder = TypeFolder { tf_view = noView
                             , tf_tyvar = do_tv
                             , tf_tybinder = do_bndr }
  where
    do_tv is v = Endo do_it
      where
        do_it acc | v `elemVarSet` is = acc
                  | v `elemVarSet` acc = acc
                  | otherwise = acc `extendVarSet` v
    do_bndr is tv _ = extendVarSet is tv

{- *********************************************************************
*                                                                      *
          The FV versions return deterministic results
*                                                                      *
********************************************************************* -}

tyKiVarsOfTypeDSet :: Type -> DVarSet
tyKiVarsOfTypeDSet ty = fvDVarSet $ tyKiFVsOfType ty

tyKiVarsOfTypeList :: Type -> [Var]
tyKiVarsOfTypeList ty = fvVarList $ tyKiFVsOfType ty

tyKiFVsOfType :: Type -> FV
tyKiFVsOfType (TyVarTy v) f bound_vars (acc_list, acc_set)
  | not (f v) = (acc_list, acc_set)
  | v `elemVarSet` bound_vars = (acc_list, acc_set)
  | v `elemVarSet` acc_set = (acc_list, acc_set)
  | otherwise = kiFVsOfKind (tyVarKind v) f emptyVarSet (v:acc_list, extendVarSet acc_set v)
tyKiFVsOfType (TyConApp _ tys) f bound_vars acc = tyKiFVsOfTypes tys f bound_vars acc
tyKiFVsOfType (AppTy fun arg) f bound_vars acc
  = (tyKiFVsOfType fun `unionFV` tyKiFVsOfType arg) f bound_vars acc
tyKiFVsOfType (FunTy k arg res) f bound_vars acc
  = (kiFVsOfKind k `unionFV` tyKiFVsOfType arg `unionFV` tyKiFVsOfType res) f bound_vars acc
tyKiFVsOfType (ForAllTy bndr ty) f bound_vars acc
  = tyKiFVsBndr bndr (tyKiFVsOfType ty) f bound_vars acc
tyKiFVsOfType (TyLamTy v ty) f bound_vars acc
  = tyKiFVsVarBndr v (tyKiFVsOfType ty) f bound_vars acc
tyKiFVsOfType other _ _ _  = pprPanic "tyKiFVsOfType" (ppr other)

tyKiFVsBndr :: ForAllTyBinder -> FV -> FV
tyKiFVsBndr (Bndr tv _) fvs = tyKiFVsVarBndr tv fvs

tyKiFVsVarBndr :: Var -> FV -> FV
tyKiFVsVarBndr var fvs = kiFVsOfKind (varKind var) `unionFV` delFV var fvs

tyKiFVsOfTypes :: [Type] -> FV
tyKiFVsOfTypes [] fv_cand in_scope acc = emptyFV fv_cand in_scope acc
tyKiFVsOfTypes (ty:tys) fv_cand in_scope acc
  = (tyKiFVsOfType ty `unionFV` tyKiFVsOfTypes tys) fv_cand in_scope acc
{- *********************************************************************
*                                                                      *
            Free type constructors
*                                                                      *
********************************************************************* -}

tyConsOfType :: Type -> UniqSet TyCon
tyConsOfType ty = go ty
  where
    go :: Type -> UniqSet TyCon
    go ty | Just ty' <- coreView ty = go ty'
    go (TyVarTy {}) = emptyUniqSet
    go (TyConApp tc tys) = go_tc tc `unionUniqSets` tyConsOfTypes tys
    go (AppTy a b) = go a `unionUniqSets` go b
    go (FunTy _ a b) = go a `unionUniqSets` go b
    go (ForAllTy _ ty) = go ty
    go (TyLamTy _ ty) = go ty
    go other = pprPanic "tyConsOfType" (ppr other)

    go_tc tc = unitUniqSet tc

tyConsOfTypes :: [Type] -> UniqSet TyCon
tyConsOfTypes tys = foldr (unionUniqSets . tyConsOfType) emptyUniqSet tys
