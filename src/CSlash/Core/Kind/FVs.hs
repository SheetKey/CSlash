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
import CSlash.Utils.FV
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
          Deep free variables
*                                                                      *
********************************************************************* -}

kiVarsOfKind :: Kind -> KdVarSet
kiVarsOfKind ki = runKdVars (deep_ki ki)

kiVarsOfKinds :: [Kind] -> KdVarSet
kiVarsOfKinds kis = runKdVars (deep_kis kis)

deep_ki :: Kind -> Endo KdVarSet
deep_kis :: [Kind] -> Endo KdVarSet
(deep_ki, deep_kis) = foldKind deepKvFolder emptyVarSet

deepKvFolder :: KindFolder KdVarSet (Endo KdVarSet)
deepKvFolder = KindFolder { kf_view = noKindView
                          , kf_kivar = do_kv
                          , kf_UKd = mempty
                          , kf_AKd = mempty
                          , kf_LKd = mempty
                          , kf_ctxt = do_ctxt }
  where
    do_kv is v = Endo do_it
      where
        do_it acc | v `elemVarSet` is = acc
                  | v `elemVarSet` acc = acc
                  | otherwise = acc `extendVarSet` v

    do_ctxt is ctxt = Endo do_it
      where
        get_kinds (LTKd k1 k2) = [k1, k2]
        get_kinds (LTEQKd k1 k2) = [k1, k2]

        kinds = concatMap get_kinds ctxt

        kvs = kiVarsOfKinds kinds

        do_it acc = let kvs' = kvs `minusVarSet` is
                    in acc `unionVarSet` kvs'

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
                             , kf_kivar = do_kv
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

{- *********************************************************************
*                                                                      *
          The FV versions return deterministic results
*                                                                      *
********************************************************************* -}

kiVarsOfKindDSet :: Kind -> DKiVarSet 
kiVarsOfKindDSet ki = fvDVarSet $ kiFVsOfKind ki

kiVarsOfKindList :: Kind -> [KindVar]
kiVarsOfKindList ki = fvVarList $ kiFVsOfKind ki

kiFVsOfKind :: Kind -> FV
kiFVsOfKind (KiVarKi v) f bound_vars (acc_list, acc_set)
  | not (f v) = (acc_list, acc_set)
  | v `elemVarSet` bound_vars = (acc_list, acc_set)
  | v `elemVarSet` acc_set = (acc_list, acc_set)
  | otherwise = (v:acc_list, extendVarSet acc_set v)
kiFVsOfKind UKd _ _ acc = acc
kiFVsOfKind AKd _ _ acc = acc
kiFVsOfKind LKd _ _ acc = acc
kiFVsOfKind (FunKd _ arg res) f bound_var acc
  = (kiFVsOfKind arg `unionFV` kiFVsOfKind res) f bound_var acc
kiFVsOfKind (KdContext rels) f bound_vars acc = (mapUnionFV go_rel rels) f bound_vars acc
  where
    go_rel (LTKd k1 k2) f bound_vars acc
      = (kiFVsOfKind k1 `unionFV` kiFVsOfKind k2) f bound_vars acc
    go_rel (LTEQKd k1 k2) f bound_vars acc
      = (kiFVsOfKind k1 `unionFV` kiFVsOfKind k2) f bound_vars acc

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
                                , kf_UKd = Any False
                                , kf_AKd = Any False
                                , kf_LKd = Any False
                                , kf_ctxt = \_ _ -> Any False }

anyFreeVarsOfKind :: (KindVar -> Bool) -> Kind -> Bool
anyFreeVarsOfKind check_fv ki = DM.getAny (f ki)
  where (f, _) = foldKind (afvFolder check_fv) emptyVarSet
