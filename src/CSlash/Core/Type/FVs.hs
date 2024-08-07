module CSlash.Core.Type.FVs where

import Data.Monoid as DM ( Endo(..), Any(..) )
import CSlash.Core.Type.Rep
import CSlash.Core.TyCon

import CSlash.Types.Var
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Set

import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Utils.Misc
import CSlash.Utils.Panic

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
