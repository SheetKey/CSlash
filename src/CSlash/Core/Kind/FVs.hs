module CSlash.Core.Kind.FVs where

import Data.Monoid as DM ( Endo(..), Any(..) )
import CSlash.Core.Kind
import CSlash.Core.TyCon

import CSlash.Types.Var
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Set

import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Utils.Misc
import CSlash.Utils.Panic

{- *********************************************************************
*                                                                      *
          Endo for free variables
*                                                                      *
********************************************************************* -}

runKdVars :: Endo KdVarSet -> KdVarSet
{-# INLINE runKdVars #-}
runKdVars f = appEndo f emptyVarSet

{- *********************************************************************
*                                                                      *
          Shallow free variables
*                                                                      *
********************************************************************* -}

shallowKdVarsOfKind :: Kind -> KdVarSet
shallowKdVarsOfKind kd = runKdVars (shallow_kd kd)

shallowKdVarsOfKinds :: [Kind] -> KdVarSet
shallowKdVarsOfKinds kds = runKdVars (shallow_kds kds)

shallowKdVarsOfKdVarEnv :: KdVarEnv Kind -> KdVarSet
shallowKdVarsOfKdVarEnv kds = shallowKdVarsOfKinds (nonDetEltsUFM kds)

shallow_kd :: Kind -> Endo KdVarSet
shallow_kds :: [Kind] -> Endo KdVarSet

(shallow_kd, shallow_kds) = foldKind shallowKvFolder emptyVarSet

shallowKvFolder :: KindFolder KdVarSet (Endo KdVarSet)
shallowKvFolder = KindFolder { kf_view = noKindView
                             , kf_kdvar = do_kv
                             , kf_UKd = mempty
                             , kf_AKd = mempty
                             , kf_LKd = mempty
                             , kf_ctxt = do_ctxt
                             }
  where
    do_kv is v = Endo do_it
      where
        do_it acc | v `elemVarSet` is = acc
                  | v `elemVarSet` acc = acc
                  | otherwise = acc `extendVarSet` v
    do_ctxt _ _ = mempty
