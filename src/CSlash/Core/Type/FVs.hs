{-# LANGUAGE TypeAbstractions #-}
module CSlash.Core.Type.FVs where

import {-# SOURCE #-} CSlash.Core.Type (coreView)

import Data.Monoid as DM ( Endo(..), Any(..) )
import CSlash.Core.Type.Rep
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs hiding (fvsVarBndr)
import CSlash.Core.TyCon

import CSlash.Types.Var
import CSlash.Types.Unique
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

runTyVars :: Endo (VarSet tv kv) -> VarSet tv kv
{-# INLINE runTyVars #-}
runTyVars f = appEndo f emptyVarSet

{- *********************************************************************
*                                                                      *
          Deep free variables
*                                                                      *
********************************************************************* -}

deep_ty
  :: (Outputable tv, Outputable kv, Uniquable tv, Uniquable kv, VarHasKind tv kv)
  => Type tv kv -> Endo (MkVarSet tv, MkVarSet kv)
deep_ty = fst $ foldType deepTvFolder (emptyVarSet, emptyVarSet)

deep_tys
  :: (Outputable tv, Outputable kv, Uniquable tv, Uniquable kv, VarHasKind tv kv)
  => [Type tv kv] -> Endo (MkVarSet tv, MkVarSet kv)
deep_tys = snd $ foldType deepTvFolder (emptyVarSet, emptyVarSet)

deepTvFolder
  :: (Outputable tv, Outputable kv, Uniquable tv, Uniquable kv, VarHasKind tv kv)
  => TypeFolder tv kv (MkVarSet tv, MkVarSet kv) (MkVarSet kv) (Endo (MkVarSet tv, MkVarSet kv))
deepTvFolder = TypeFolder { tf_view = noView
                          , tf_tyvar = do_tv
                          , tf_tybinder = do_bndr
                          , tf_tylambinder = do_tylambndr
                          , tf_tylamkibinder = do_kilambndr
                          , tf_swapEnv = snd
                          , tf_mkcf = deepMKcvFolder }
  where
    --do_tv :: (MkVarSet tv, MkVarSet kv) -> tv -> Endo (MkVarSet tv, MkVarSet kv)
    do_tv (tis, _) v = Endo do_it
      where
        do_it acc@(tacc, kacc)
          | v `elemVarSet` tis = acc
          | v `elemVarSet` tacc = acc
          | otherwise = appEndo (deep_mki (varKind v))
                        $ (tacc `extendVarSet` v, kacc)
          -- see GHC note [Closing over free variable kinds] for justification of deep_mki
          -- (deep_mki starts with emptyVarSet as in_scope set)
    do_bndr (tis, kis) tv _ = (extendVarSet tis tv, kis)
    do_tylambndr (tis, kis) tv = (extendVarSet tis tv, kis)
    do_kilambndr (tis, kis) kv = (tis, extendVarSet kis kv)

{- *********************************************************************
*                                                                      *
          Shallow free variables
*                                                                      *
********************************************************************* -}

shallow_ty
  :: (Outputable tv, Outputable kv, Uniquable tv, Uniquable kv, VarHasKind tv kv)
  => Type tv kv -> Endo (MkVarSet tv, MkVarSet kv)
shallow_ty = fst $ foldType shallowTvFolder (emptyVarSet, emptyVarSet)

shallow_tys
  :: (Outputable tv, Outputable kv, Uniquable tv, Uniquable kv, VarHasKind tv kv)
  => [Type tv kv] -> Endo (MkVarSet tv, MkVarSet kv)
shallow_tys = snd $ foldType shallowTvFolder (emptyVarSet, emptyVarSet)

shallowTvFolder
  :: (Outputable tv, Outputable kv, Uniquable tv, Uniquable kv, VarHasKind tv kv)
  => TypeFolder tv kv (MkVarSet tv, MkVarSet kv) (MkVarSet kv) (Endo (MkVarSet tv, MkVarSet kv))
shallowTvFolder = TypeFolder { tf_view = noView
                             , tf_tyvar = do_tv
                             , tf_tybinder = do_bndr
                             , tf_tylambinder = do_tylambndr
                             , tf_tylamkibinder = do_kilambndr
                             , tf_swapEnv = snd
                             , tf_mkcf = shallowMKcvFolder }
  where
    do_tv (tis, _) v = Endo do_it
      where
        do_it acc@(tacc, kacc)
          | v `elemVarSet` tis = acc
          | v `elemVarSet` tacc = acc
          | otherwise = (tacc `extendVarSet` v, kacc)
    do_bndr (tis, kis) tv _ = (extendVarSet tis tv, kis)
    do_tylambndr (tis, kis) tv = (extendVarSet tis tv, kis)
    do_kilambndr (tis, kis) kv = (tis, extendVarSet kis kv)

{- *********************************************************************
*                                                                      *
          The FV versions return deterministic results
*                                                                      *
********************************************************************* -}

type TyFV tv kv = FV (Type tv kv)

liftKiFV :: KiFV kv -> TyFV tv kv
liftKiFV kfv f (tis, kis) (taccl, taccs, kaccl, kaccs)
  = case kfv (f . Right) kis (kaccl, kaccs) of
      (kaccl, kaccs) -> (taccl, taccs, kaccl, kaccs)

fvsOfType
  :: (Outputable tv, Outputable kv, Uniquable tv, Uniquable kv, VarHasKind tv kv)
  => Type tv kv -> TyFV tv kv

fvsOfType (TyVarTy v) f (bound_vars, bks) acc@(acc_list, acc_set, kl, ks)
  | not (f (Left v)) = acc
  | v `elemVarSet` bound_vars = acc
  | v `elemVarSet` acc_set = acc
  | otherwise = case fvsOfMonoKind (varKind v) (f . Right) emptyVarSet (kl, ks) of
                  (kl, ks) -> (v:acc_list, extendVarSet acc_set v, kl, ks)

fvsOfType (TyConApp _ tys) f bound_vars acc = fvsOfTypes tys f bound_vars acc

fvsOfType (AppTy fun arg) f bound_vars acc
  = (fvsOfType fun `unionFV` fvsOfType arg) f bound_vars acc

fvsOfType (FunTy k arg res) f bound_vars acc
  = (liftKiFV (fvsOfMonoKind k) `unionFV` fvsOfType arg `unionFV` fvsOfType res)
    f bound_vars acc

fvsOfType (ForAllTy bndr ty) f bound_vars acc
  = fvsBndr bndr (fvsOfType ty) f bound_vars acc

fvsOfType (TyLamTy v ty) f bound_vars acc
  = fvsVarBndr v (fvsOfType ty) f bound_vars acc

fvsOfType other _ _ _  = pprPanic "fvsOfType" (ppr other)

fvsBndr
  :: (Uniquable tv, Uniquable kv, VarHasKind tv kv)
  => ForAllBinder tv -> TyFV tv kv -> TyFV tv kv
fvsBndr (Bndr tv _) fvs = fvsVarBndr tv fvs

fvsVarBndrs
  :: (Uniquable tv, Uniquable kv, VarHasKind tv kv)
  => [tv] -> TyFV tv kv -> TyFV tv kv
fvsVarBndrs vars fvs = foldr fvsVarBndr fvs vars

fvsVarBndr
  :: (Uniquable tv, Uniquable kv, VarHasKind tv kv)
  => tv -> TyFV tv kv -> TyFV tv kv
fvsVarBndr var fvs = liftKiFV (fvsOfMonoKind (varKind var)) `unionFV` delFV (Left var) fvs

fvsOfTypes
  :: (Outputable tv, Outputable kv, Uniquable tv, Uniquable kv, VarHasKind tv kv)
  => [Type tv kv] -> TyFV tv kv
fvsOfTypes [] fv_cand in_scope acc = emptyFV fv_cand in_scope acc
fvsOfTypes (ty:tys) fv_cand in_scope acc
  = (fvsOfType ty `unionFV` fvsOfTypes tys) fv_cand in_scope acc

{- *********************************************************************
*                                                                      *
            Free type constructors
*                                                                      *
********************************************************************* -}

tyConsOfType
  :: (Outputable tv, Outputable kv)
  => Type tv kv -> UniqSet (TyCon tv kv)
tyConsOfType ty = go ty
  where
    -- go :: Type -> UniqSet TyCon
    go ty | Just ty' <- coreView ty = go ty'
    go (TyVarTy {}) = emptyUniqSet
    go (TyConApp tc tys) = go_tc tc `unionUniqSets` tyConsOfTypes tys
    go (AppTy a b) = go a `unionUniqSets` go b
    go (FunTy _ a b) = go a `unionUniqSets` go b
    go (ForAllTy _ ty) = go ty
    go (TyLamTy _ ty) = go ty
    go other = pprPanic "tyConsOfType" (ppr other)

    go_tc tc = unitUniqSet tc

tyConsOfTypes
  :: (Outputable tv, Outputable kv)
  => [Type tv kv] -> UniqSet (TyCon tv kv)
tyConsOfTypes tys = foldr (unionUniqSets . tyConsOfType) emptyUniqSet tys
