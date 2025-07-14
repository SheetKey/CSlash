{-# LANGUAGE TypeAbstractions #-}
module CSlash.Core.Type.FVs where

import {-# SOURCE #-} CSlash.Core.Type (coreView)

import Data.Monoid as DM ( Endo(..), Any(..) )
import CSlash.Core.Type.Rep
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs hiding (fvsVarBndr, afvFolder)
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

runTyKiVars
  :: Endo (MkVarSet tv, MkVarSet (KiCoVar kv), MkVarSet kv)
  -> (MkVarSet tv, MkVarSet (KiCoVar kv), MkVarSet kv)
{-# INLINE runTyKiVars #-}
runTyKiVars f = appEndo f (emptyVarSet, emptyVarSet, emptyVarSet)

{- *********************************************************************
*                                                                      *
          Deep free variables
*                                                                      *
********************************************************************* -}

varsOfType
  :: VarHasKind tv kv
  => Type tv kv
  -> (MkVarSet tv, MkVarSet (KiCoVar kv), MkVarSet kv)
varsOfType ty = runTyKiVars (deep_ty ty)

varsOfTypes
  :: VarHasKind tv kv
  => [Type tv kv]
  -> (MkVarSet tv, MkVarSet (KiCoVar kv), MkVarSet kv)
varsOfTypes tys = runTyKiVars (deep_tys tys)

deep_ty
  :: VarHasKind tv kv
  => Type tv kv
  -> Endo (MkVarSet tv, MkVarSet (KiCoVar kv), MkVarSet kv)
deep_ty = fst $ foldType deepTvFolder (emptyVarSet, emptyVarSet, emptyVarSet)

deep_tys
  :: VarHasKind tv kv
  => [Type tv kv]
  -> Endo (MkVarSet tv, MkVarSet (KiCoVar kv), MkVarSet kv)
deep_tys = snd $ foldType deepTvFolder (emptyVarSet, emptyVarSet, emptyVarSet)

deepTvFolder
  :: VarHasKind tv kv
  => TypeFolder tv kv
     (MkVarSet tv, MkVarSet (KiCoVar kv), MkVarSet kv)
     (MkVarSet (KiCoVar kv), MkVarSet kv)
     (Endo (MkVarSet (KiCoVar kv), MkVarSet kv))
     (Endo (MkVarSet tv, MkVarSet (KiCoVar kv), MkVarSet kv))
deepTvFolder = TypeFolder { tf_view = noView
                          , tf_tyvar = do_tv
                          , tf_tybinder = do_bndr
                          , tf_tylambinder = do_tylambndr
                          , tf_tylamkibinder = do_kilambndr
                          , tf_swapEnv = \(_, kcv, kv) -> (kcv, kv)
                          , tf_embedKiRes = \(Endo f) -> Endo $ \(tv, kcv, kv) ->
                              let (kcv', kv') = f (kcv, kv)
                              in (tv, kcv', kv')
                          , tf_mkcf = deepMKcvFolder }
  where
    do_tv (tis, _, _) v = Endo do_it
      where
        do_it acc@(tacc, kcvacc, kacc)
          | v `elemVarSet` tis = acc
          | v `elemVarSet` tacc = acc
          | Just v' <- toKiCoVar_maybe v
          = let (kcvacc', kacc') = appEndo (deep_mki (varKind v))
                                   (kcvacc `extendVarSet` v', kacc)
            in (tacc, kcvacc', kacc')
          | otherwise = let (kcvacc', kacc') = appEndo (deep_mki (varKind v)) (kcvacc, kacc)
                        in (tacc `extendVarSet` v, kcvacc', kacc')
          -- see GHC note [Closing over free variable kinds] for justification of deep_mki
          -- (deep_mki starts with emptyVarSet as in_scope set)
    do_bndr (tis, kcvis, kis) tv _
      | Just kcv <- toKiCoVar_maybe tv
      = (extendVarSet tis tv, extendVarSet kcvis kcv, kis)
      | otherwise
      = (extendVarSet tis tv, kcvis, kis)
    do_tylambndr (tis, kcvis, kis) tv
      | Just kcv <- toKiCoVar_maybe tv
      = (extendVarSet tis tv, extendVarSet kcvis kcv, kis)
      | otherwise
      = (extendVarSet tis tv, kcvis, kis)
    do_kilambndr (tis, kcvis, kis) kv = (tis, kcvis, extendVarSet kis kv)

{- *********************************************************************
*                                                                      *
          Shallow free variables
*                                                                      *
********************************************************************* -}

shallowVarsOfTypes
  :: VarHasKind tv kv
  => [Type tv kv]
  -> (MkVarSet tv, MkVarSet (KiCoVar kv), MkVarSet kv)
shallowVarsOfTypes tys = runTyKiVars (shallow_tys tys)

shallowVarsOfTyVarEnv
  :: VarHasKind tv kv
  => MkVarEnv tv (Type tv kv)
  -> (MkVarSet tv, MkVarSet (KiCoVar kv), MkVarSet kv)
shallowVarsOfTyVarEnv tys = shallowVarsOfTypes (nonDetEltsUFM tys)

shallow_ty
  :: VarHasKind tv kv
  => Type tv kv
  -> Endo (MkVarSet tv, MkVarSet (KiCoVar kv), MkVarSet kv)
shallow_ty = fst $ foldType shallowTvFolder (emptyVarSet, emptyVarSet, emptyVarSet)

shallow_tys
  :: VarHasKind tv kv
  => [Type tv kv]
  -> Endo (MkVarSet tv, MkVarSet (KiCoVar kv), MkVarSet kv)
shallow_tys = snd $ foldType shallowTvFolder (emptyVarSet, emptyVarSet, emptyVarSet)

shallowTvFolder
  :: VarHasKind tv kv
  => TypeFolder tv kv
     (MkVarSet tv, MkVarSet (KiCoVar kv), MkVarSet kv)
     (MkVarSet (KiCoVar kv), MkVarSet kv)
     (Endo (MkVarSet (KiCoVar kv), MkVarSet kv))
     (Endo (MkVarSet tv, MkVarSet (KiCoVar kv), MkVarSet kv))
shallowTvFolder = TypeFolder { tf_view = noView
                             , tf_tyvar = do_tv
                             , tf_tybinder = do_bndr
                             , tf_tylambinder = do_tylambndr
                             , tf_tylamkibinder = do_kilambndr
                             , tf_swapEnv = \(_, kcv, kv) -> (kcv, kv)
                             , tf_embedKiRes = \(Endo f) -> Endo $ \(tv, kcv, kv) ->
                                 let (kcv', kv') = f (kcv, kv)
                                 in (tv, kcv', kv')
                             , tf_mkcf = shallowMKcvFolder }
  where
    do_tv (tis, _, _) v = Endo do_it
      where
        do_it acc@(tacc, kcvacc, kacc)
          | v `elemVarSet` tis = acc
          | v `elemVarSet` tacc = acc
          | Just v' <- toKiCoVar_maybe v
          = (tacc, kcvacc `extendVarSet` v', kacc)
          | otherwise = (tacc `extendVarSet` v, kcvacc, kacc)
    do_bndr (tis, kcvis, kis) tv _
      | Just kcv <- toKiCoVar_maybe tv
      = (extendVarSet tis tv, extendVarSet kcvis kcv, kis)
      | otherwise
      = (extendVarSet tis tv, kcvis, kis)
    do_tylambndr (tis, kcvis, kis) tv
      | Just kcv <- toKiCoVar_maybe tv
      = (extendVarSet tis tv, extendVarSet kcvis kcv, kis)
      | otherwise
      = (extendVarSet tis tv, kcvis, kis)
    do_kilambndr (tis, kcvis, kis) kv = (tis, kcvis, extendVarSet kis kv)

{- *********************************************************************
*                                                                      *
          The FV versions return deterministic results
*                                                                      *
********************************************************************* -}

-- unionTyKiFV :: TyFV tv kv -> KiFV kv -> TyFV tv kv
-- unionTyKiFV tyfv kifv f is@(_, bks) (tl, ts, kl, ks)
--   = case kifv (f . Right) bks $! (kl, ks) of
--       (kl, ks) -> tyfv f is $! (tl, ts, kl, ks)

type TyFV tv kv = FV (Type tv kv)

liftKiFV :: KiFV kv -> TyFV tv kv
liftKiFV kfv f (tis, kis) (taccl, taccs, kaccl, kaccs)
  = case kfv (f . Right) kis (kaccl, kaccs) of
      (kaccl, kaccs) -> (taccl, taccs, kaccl, kaccs)

fvsOfType
  :: IsTyVar tv kv
  => Type tv kv -> TyFV tv kv

fvsOfType (TyVarTy v) f (bound_vars, bks) acc@(acc_list, acc_set, kl, ks)
  | not (f (Left v)) = acc
  | v `elemVarSet` bound_vars = acc
  | v `elemVarSet` acc_set = acc
  | otherwise = liftKiFV (fvsOfMonoKind (varKind v)) f (bound_vars, bks)
                (v:acc_list, extendVarSet acc_set v, kl, ks)

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

fvsOfType (BigTyLamTy kv ty) f bound_vars acc
  = delFV (Right kv) (fvsOfType ty) f bound_vars acc

fvsOfType (CastTy ty kco) f bound_vars acc
  = (fvsOfType ty `unionFV` fvsOfKiCo kco) f bound_vars acc

fvsOfType (KindCoercion kco) f bound_vars acc = fvsOfKiCo kco f bound_vars acc

fvsOfType (Embed ki) f bound_vars acc = liftKiFV (fvsOfMonoKind ki) f bound_vars acc

fvsOfKiCo :: IsTyVar tv kv => KindCoercion kv -> TyFV tv kv
fvsOfKiCo (Refl ki) f bound_vars acc = liftKiFV (fvsOfMonoKind ki) f bound_vars acc
fvsOfKiCo BI_U_A f bound_vars acc = acc
fvsOfKiCo BI_A_L f bound_vars acc = acc
fvsOfKiCo (BI_U_LTEQ ki) f bound_vars acc = liftKiFV (fvsOfMonoKind ki) f bound_vars acc
fvsOfKiCo (BI_LTEQ_L ki) f bound_vars acc = liftKiFV (fvsOfMonoKind ki) f bound_vars acc
fvsOfKiCo (LiftEq co) f bound_vars acc = fvsOfKiCo co f bound_vars acc
fvsOfKiCo (LiftLT co) f bound_vars acc = fvsOfKiCo co f bound_vars acc
fvsOfKiCo (FunCo { fco_arg = co1, fco_res = co2 }) f bound_vars acc
  = (fvsOfKiCo co1 `unionFV` fvsOfKiCo co2) f bound_vars acc
fvsOfKiCo (KiCoVarCo kcv) f bound_vars acc = fvsOfKiCoVar kcv f bound_vars acc
fvsOfKiCo (HoleCo h) f bound_vars acc = fvsOfKiCoVar (coHoleCoVar h) f bound_vars acc
fvsOfKiCo (SymCo co) f bound_vars acc = fvsOfKiCo co f bound_vars acc
fvsOfKiCo (TransCo co1 co2) f bound_vars acc
  = (fvsOfKiCo co1 `unionFV` fvsOfKiCo co2) f bound_vars acc

fvsOfKiCoVar :: IsTyVar tv kv => KiCoVar kv -> TyFV tv kv
fvsOfKiCoVar _v f (bound_vars, bks) acc@(acc_list, acc_set, kl, ks)
  | not (f (Left v)) = acc
  | v `elemVarSet` bound_vars = acc
  | v `elemVarSet` acc_set = acc
  | otherwise = liftKiFV (fvsOfMonoKind (varKind v))
                f (bound_vars, bks) (v:acc_list, extendVarSet acc_set v, kl, ks)
  where
    v = toGenericTyVar _v

fvsOfKiCos :: IsTyVar tv kv => [KindCoercion kv] -> TyFV tv kv
fvsOfKiCos [] f bound_vars acc = emptyFV f bound_vars acc
fvsOfKiCos (co:cos) f bound_vars acc = (fvsOfKiCo co `unionFV` fvsOfKiCos cos) f bound_vars acc

fvsBndr
  :: VarHasKind tv kv
  => ForAllBinder tv -> TyFV tv kv -> TyFV tv kv
fvsBndr (Bndr tv _) fvs = fvsVarBndr tv fvs

fvsVarBndrs
  :: VarHasKind tv kv
  => [tv] -> TyFV tv kv -> TyFV tv kv
fvsVarBndrs vars fvs = foldr fvsVarBndr fvs vars

fvsVarBndr
  :: VarHasKind tv kv
  => tv -> TyFV tv kv -> TyFV tv kv
fvsVarBndr var fvs = liftKiFV (fvsOfMonoKind (varKind var)) `unionFV` delFV (Left var) fvs

fvsKiVarBndrs :: VarHasKind tv kv => [kv] -> TyFV tv kv -> TyFV tv kv
fvsKiVarBndrs vars fvs = foldr fvsKiVarBndr fvs vars

fvsKiVarBndr :: VarHasKind tv kv => kv -> TyFV tv kv -> TyFV tv kv
fvsKiVarBndr var fvs = delFV (Right var) fvs

fvsOfTypes
  :: IsTyVar tv kv
  => [Type tv kv] -> TyFV tv kv
fvsOfTypes [] fv_cand in_scope acc = emptyFV fv_cand in_scope acc
fvsOfTypes (ty:tys) fv_cand in_scope acc
  = (fvsOfType ty `unionFV` fvsOfTypes tys) fv_cand in_scope acc

varsOfTypeDSet :: IsTyVar tv kv => Type tv kv -> (MkDVarSet tv, MkDVarSet kv)
varsOfTypeDSet ty = case fvVarAcc (fvsOfType ty) of
  (tvs, _, kvs, _) -> (mkDVarSet tvs, mkDVarSet kvs)

varsOfTypeList :: IsTyVar tv kv => Type tv kv -> ([tv], [kv])
varsOfTypeList ty = case fvVarAcc (fvsOfType ty) of
  (tvs, _, kvs, _) -> (tvs, kvs)

varsOfTypesList :: IsTyVar tv kv => [Type tv kv] -> ([tv], [kv])
varsOfTypesList tys = case fvVarAcc (fvsOfTypes tys) of
  (tvs, _, kvs, _) -> (tvs, kvs)

typeSomeFreeVars
  :: IsTyVar tv kv
  => (Either tv kv -> Bool) -> Type tv kv -> (MkVarSet tv, MkVarSet kv)
typeSomeFreeVars fv_cand ty = case fvVarAcc (filterFV fv_cand $ fvsOfType ty) of
  (_, tvs, _, kvs) -> (tvs, kvs)

{- *********************************************************************
*                                                                      *
            Any free vars
*                                                                      *
********************************************************************* -}

afvFolder
  :: IsTyVar tv kv
  => (tv -> Bool) -> (KiCoVar kv -> Bool) -> (kv -> Bool)
  -> TypeFolder tv kv
     (MkVarSet tv, MkVarSet (KiCoVar kv), MkVarSet kv)
     (MkVarSet (KiCoVar kv), MkVarSet kv)
     DM.Any DM.Any
afvFolder f_tv f_kcv f_kv = TypeFolder { tf_view = noView
                                 , tf_tyvar = do_tyvar
                                 , tf_tybinder = do_bndr
                                 , tf_tylambinder = do_tylambndr
                                 , tf_tylamkibinder = do_kilambndr
                                 , tf_swapEnv = \(_, kcv, kv) -> (kcv, kv)
                                 , tf_embedKiRes = id
                                 , tf_mkcf = mafvFolder f_kcv f_kv }
  where
    do_tyvar (is, _, _) tv = Any (not (tv `elemVarSet` is) && f_tv tv)
    do_bndr (is, kcvs, kvs) tv _
      | Just kcv <- toKiCoVar_maybe tv
      = (is `extendVarSet` tv, kcvs `extendVarSet` kcv, kvs)
      | otherwise
      = (is `extendVarSet` tv, kcvs, kvs)
    do_tylambndr (is, kcvs, kvs) tv
      | Just kcv <- toKiCoVar_maybe tv
      = (is `extendVarSet` tv, kcvs `extendVarSet` kcv, kvs)
      | otherwise
      = (is `extendVarSet` tv, kcvs, kvs)
    do_kilambndr (tv, kcv, is) kv = (tv, kcv, is `extendVarSet` kv)

noFreeVarsOfType :: IsTyVar tv kv => Type tv kv -> Bool
noFreeVarsOfType ty = not $ DM.getAny (f ty)
  where (f, _) = foldType (afvFolder (const True) (const True) (const True))
                 (emptyVarSet, emptyVarSet, emptyVarSet)

{- *********************************************************************
*                                                                      *
            Free type constructors
*                                                                      *
********************************************************************* -}

tyConsOfType
  :: IsTyVar tv kv
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
  :: IsTyVar tv kv
  => [Type tv kv] -> UniqSet (TyCon tv kv)
tyConsOfTypes tys = foldr (unionUniqSets . tyConsOfType) emptyUniqSet tys
