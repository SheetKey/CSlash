{-# LANGUAGE TypeAbstractions #-}
module CSlash.Core.Type.FVs where

import {-# SOURCE #-} CSlash.Core.Type (coreView)
import {-# SOURCE #-} CSlash.Core.Type

import Data.Monoid as DM ( Endo(..), Any(..) )
import CSlash.Core.Type.Rep
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs hiding (fvsVarBndr, afvFolder, runCoVars)
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
  :: Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
  -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
{-# INLINE runTyKiVars #-}
runTyKiVars f = appEndo f (emptyVarSet, emptyVarSet, emptyVarSet)

runCoVars
  :: Endo (TyCoVarSet p, KiCoVarSet p)
  -> (TyCoVarSet p, KiCoVarSet p)
{-# INLINE runCoVars #-}
runCoVars f = appEndo f (emptyVarSet, emptyVarSet)

{- *********************************************************************
*                                                                      *
          Deep free variables
*                                                                      *
********************************************************************* -}

varsOfTyVarEnv :: VarEnv (TyVar p') (Type p) -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
varsOfTyVarEnv tys = varsOfTypes (nonDetEltsUFM tys)

varsOfType :: Type p -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
varsOfType ty = runTyKiVars (deep_ty ty)

varsOfTypes :: [Type p] -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
varsOfTypes tys = runTyKiVars (deep_tys tys)

deep_ty :: Type p -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
deep_ty = case foldTyCo deepTvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (f, _, _, _) -> f

deep_tys :: [Type p]
  -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
deep_tys = case foldTyCo deepTvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, f, _, _) -> f

deepTvFolder
  :: TyCoFolder p
     (TyVarSet p, KiCoVarSet p, KiVarSet p)
     (KiCoVarSet p, KiVarSet p)
     (Endo (KiCoVarSet p, KiVarSet p))
     (Endo (TyVarSet p, KiCoVarSet p, KiVarSet p))
deepTvFolder = TyCoFolder { tcf_view = noView
                          , tcf_tyvar = do_tv
                          , tcf_covar = panic "deepTvFolder do_covar"
                          , tcf_hole = panic "deepTvFolder do_hole"
                          , tcf_tybinder = do_bndr
                          , tcf_kcobinder = do_bndr_kco
                          , tcf_tylambinder = do_tylambndr
                          , tcf_tylamkibinder = do_kilambndr
                          , tcf_swapEnv = \(_, kcv, kv) -> (kcv, kv)
                          , tcf_embedKiRes = \(Endo f) -> Endo $ \(tv, kcv, kv) ->
                              let (kcv', kv') = f (kcv, kv)
                              in (tv, kcv', kv')
                          , tcf_mkcf = deepMKcvFolder }
  where
    do_tv (tis, _, _) v = Endo do_it
      where
        do_it acc@(tacc, kcvacc, kacc)
          | v `elemVarSet` tis = acc
          | v `elemVarSet` tacc = acc
          | otherwise = let (kcvacc', kacc') = appEndo (deep_mki (varKind v)) (kcvacc, kacc)
                        in (tacc `extendVarSet` v, kcvacc', kacc')
          -- see GHC note [Closing over free variable kinds] for justification of deep_mki
          -- (deep_mki starts with emptyVarSet as in_scope set)
    do_bndr (tis, kcvis, kis) tv _
      = (extendVarSet tis tv, kcvis, kis)
    do_bndr_kco (tis, kcvis, kis) kcv
      = (tis, extendVarSet kcvis kcv, kis)
    do_tylambndr (tis, kcvis, kis) tv
      = (extendVarSet tis tv, kcvis, kis)
    do_kilambndr (tis, kcvis, kis) kv = (tis, kcvis, extendVarSet kis kv)

{- *********************************************************************
*                                                                      *
          Shallow free variables
*                                                                      *
********************************************************************* -}

shallowVarsOfTypes :: [Type p] -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
shallowVarsOfTypes tys = runTyKiVars (shallow_tys tys)

shallowVarsOfTyVarEnv :: VarEnv (TyVar p') (Type p) -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
shallowVarsOfTyVarEnv tys = shallowVarsOfTypes (nonDetEltsUFM tys)

shallow_ty :: Type p -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
shallow_ty = case foldTyCo shallowTvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (f, _, _, _) -> f

shallow_tys :: [Type p] -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
shallow_tys = case foldTyCo shallowTvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, f, _, _) -> f

shallowTvFolder
  :: TyCoFolder p
     (TyVarSet p, KiCoVarSet p, KiVarSet p)
     (KiCoVarSet p, KiVarSet p)
     (Endo (KiCoVarSet p, KiVarSet p))
     (Endo (TyVarSet p, KiCoVarSet p, KiVarSet p))
shallowTvFolder = TyCoFolder { tcf_view = noView
                             , tcf_tyvar = do_tv
                             , tcf_covar = panic "shallowTvFolder do_covar"
                             , tcf_hole = panic "shallowTvFolder do_hole"
                             , tcf_tybinder = do_bndr
                             , tcf_kcobinder = do_bndr_kco
                             , tcf_tylambinder = do_tylambndr
                             , tcf_tylamkibinder = do_kilambndr
                             , tcf_swapEnv = \(_, kcv, kv) -> (kcv, kv)
                             , tcf_embedKiRes = \(Endo f) -> Endo $ \(tv, kcv, kv) ->
                                 let (kcv', kv') = f (kcv, kv)
                                 in (tv, kcv', kv')
                             , tcf_mkcf = shallowMKcvFolder }
  where
    do_tv (tis, _, _) v = Endo do_it
      where
        do_it acc@(tacc, kcvacc, kacc)
          | v `elemVarSet` tis = acc
          | v `elemVarSet` tacc = acc
          | otherwise = (tacc `extendVarSet` v, kcvacc, kacc)
    do_bndr (tis, kcvis, kis) tv _
      = (extendVarSet tis tv, kcvis, kis)
    do_bndr_kco (tis, kcvis, kis) kcv
      = (tis, extendVarSet kcvis kcv, kis)
    do_tylambndr (tis, kcvis, kis) tv
      = (extendVarSet tis tv, kcvis, kis)
    do_kilambndr (tis, kcvis, kis) kv = (tis, kcvis, extendVarSet kis kv)

{- *********************************************************************
*                                                                      *
          Free coercion variables
*                                                                      *
********************************************************************* -}

coVarsOfType :: Type p -> (TyCoVarSet p, KiCoVarSet p)
coVarsOfTypes :: [Type p] -> (TyCoVarSet p, KiCoVarSet p)
coVarsOfTyCo :: TypeCoercion p -> (TyCoVarSet p, KiCoVarSet p)
coVarsOfTyCos :: [TypeCoercion p] -> (TyCoVarSet p, KiCoVarSet p)

coVarsOfType ty = runCoVars (deep_cv_ty ty)
coVarsOfTypes tys = runCoVars (deep_cv_tys tys)
coVarsOfTyCo co = runCoVars (deep_cv_co co)
coVarsOfTyCos cos = runCoVars (deep_cv_cos cos)

deep_cv_ty :: Type p -> Endo (TyCoVarSet p, KiCoVarSet p)
deep_cv_ty = case foldTyCo deepCoVarFolder (emptyVarSet, emptyVarSet) of
  (f, _, _, _) -> f

deep_cv_tys :: [Type p] -> Endo (TyCoVarSet p, KiCoVarSet p)
deep_cv_tys = case foldTyCo deepCoVarFolder (emptyVarSet, emptyVarSet) of
  (_, f, _, _) -> f

deep_cv_co :: TypeCoercion p -> Endo (TyCoVarSet p, KiCoVarSet p)
deep_cv_co = case foldTyCo deepCoVarFolder (emptyVarSet, emptyVarSet) of
  (_, _, f, _) -> f

deep_cv_cos :: [TypeCoercion p] -> Endo (TyCoVarSet p, KiCoVarSet p)
deep_cv_cos = case foldTyCo deepCoVarFolder (emptyVarSet, emptyVarSet) of
  (_, _, _, f) -> f

deepCoVarFolder
  :: TyCoFolder p
     (TyCoVarSet p, KiCoVarSet p)
     (KiCoVarSet p)
     (Endo (KiCoVarSet p))
     (Endo (TyCoVarSet p, KiCoVarSet p))
deepCoVarFolder = TyCoFolder { tcf_view = noView
                             , tcf_tyvar = do_tyvar
                             , tcf_covar = do_covar
                             , tcf_hole = do_hole
                             , tcf_tybinder = do_bndr
                             , tcf_kcobinder = do_bndr_kco
                             , tcf_tylambinder = do_tylambinder
                             , tcf_tylamkibinder = do_kilambinder
                             , tcf_swapEnv = \(_, kcv) -> kcv
                             , tcf_embedKiRes = \(Endo f) -> Endo $ \(tcv, kcv) ->
                                 let kcv' = f kcv
                                 in (tcv, kcv')
                             , tcf_mkcf = deepKiCoVarFolder
                             }
  where
    do_tyvar _ _ = mempty

    do_covar (is, _) v = Endo do_it
      where
        do_it acc@(tacc, kacc) | v `elemVarSet` is = acc
                               | v `elemVarSet` tacc = acc
                               | otherwise = appEndo (deep_cv_ty (varType v))
                                             $ (tacc `extendVarSet` v, kacc)

    do_bndr is _ _ = is
    do_bndr_kco (tis, kis) kcv
      = (tis, extendVarSet kis kcv)
    do_tylambinder is _ = is
    do_kilambinder is _ = is

    do_hole is hole = panic "do_covar is (tyCoHoleCoVar hole)"

{- *********************************************************************
*                                                                      *
          The FV versions return deterministic results
*                                                                      *
********************************************************************* -}

-- unionTyKiFV :: TyFV tv kv -> KiFV kv -> TyFV tv kv
-- unionTyKiFV tyfv kifv f is@(_, bks) (tl, ts, kl, ks)
--   = case kifv (f . Right) bks $! (kl, ks) of
--       (kl, ks) -> tyfv f is $! (tl, ts, kl, ks)

type TyFV p = FV (Type p)

liftKiFV :: KiFV p -> TyFV p
liftKiFV kfv f (_, _, kis) (taccl, taccs, kcaccl, kcaccs, kaccl, kaccs)
  = case kfv (f . In3) kis (kaccl, kaccs) of
      (kaccl, kaccs) -> (taccl, taccs, kcaccl, kcaccs, kaccl, kaccs)

fvsOfType :: Type p -> TyFV p

fvsOfType (TyVarTy v) f (bound_vars, bkcs, bks) acc@(acc_list, acc_set, kcl, kcs, kl, ks)
  | not (f (In1 v)) = acc
  | v `elemVarSet` bound_vars = acc
  | v `elemVarSet` acc_set = acc
  | otherwise = liftKiFV (fvsOfMonoKind (varKind v)) f (bound_vars, bkcs, bks)
                (v:acc_list, extendVarSet acc_set v, kcl, kcs, kl, ks)

fvsOfType (TyConApp _ tys) f bound_vars acc = fvsOfTypes tys f bound_vars acc

fvsOfType (AppTy fun arg) f bound_vars acc
  = (fvsOfType fun `unionFV` fvsOfType arg) f bound_vars acc

fvsOfType (FunTy k arg res) f bound_vars acc
  = (liftKiFV (fvsOfMonoKind k) `unionFV` fvsOfType arg `unionFV` fvsOfType res)
    f bound_vars acc

fvsOfType (ForAllTy bndr ty) f bound_vars acc
  = fvsBndr bndr (fvsOfType ty) f bound_vars acc

fvsOfType (ForAllKiCo kcv ty) f bound_vars acc
  = fvsKiCoVarBndr kcv (fvsOfType ty) f bound_vars acc

fvsOfType (TyLamTy v ty) f bound_vars acc
  = fvsVarBndr v (fvsOfType ty) f bound_vars acc

fvsOfType (BigTyLamTy kv ty) f bound_vars acc
  = delFV (In3 kv) (fvsOfType ty) f bound_vars acc

fvsOfType (CastTy ty kco) f bound_vars acc
  = (fvsOfType ty `unionFV` fvsOfKiCo kco) f bound_vars acc

fvsOfType (KindCoercion kco) f bound_vars acc = fvsOfKiCo kco f bound_vars acc

fvsOfType (Embed ki) f bound_vars acc = liftKiFV (fvsOfMonoKind ki) f bound_vars acc

fvsOfKiCo :: KindCoercion p -> TyFV p
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
fvsOfKiCo (SelCo _ co) f bound_vars acc = fvsOfKiCo co f bound_vars acc

fvsOfKiCoVar :: KiCoVar p -> TyFV p
-- fvsOfKiCoVar v f (bound_vars, bks) acc@(acc_list, acc_set, kl, ks)
--   | not (f (Left v)) = acc
--   | v `elemVarSet` bound_vars = acc
--   | v `elemVarSet` acc_set = acc
--   | otherwise = liftKiFV (fvsOfMonoKind (varKind v))
--                 f (bound_vars, bks) (v:acc_list, extendVarSet acc_set v, kl, ks)
fvsOfKiCoVar = panic "fvsOfKiCoVar"

fvsOfKiCos :: [KindCoercion p] -> TyFV p
fvsOfKiCos [] f bound_vars acc = emptyFV f bound_vars acc
fvsOfKiCos (co:cos) f bound_vars acc = (fvsOfKiCo co `unionFV` fvsOfKiCos cos) f bound_vars acc

fvsBndr :: ForAllBinder (TyVar p) -> TyFV p -> TyFV p
fvsBndr (Bndr tv _) fvs = fvsVarBndr tv fvs

fvsVarBndrs :: [TyVar p] -> TyFV p -> TyFV p
fvsVarBndrs vars fvs = foldr fvsVarBndr fvs vars

fvsVarBndr :: TyVar p -> TyFV p -> TyFV p
fvsVarBndr var fvs = liftKiFV (fvsOfMonoKind (varKind var)) `unionFV` delFV (In1 var) fvs

fvsKiCoVarBndr :: KiCoVar p -> TyFV p -> TyFV p
fvsKiCoVarBndr var fvs = liftKiFV (fvsOfMonoKind (varKind var)) `unionFV` delFV (In2 var) fvs

fvsKiVarBndrs :: [KiVar p] -> TyFV p -> TyFV p
fvsKiVarBndrs vars fvs = foldr fvsKiVarBndr fvs vars

fvsKiVarBndr :: KiVar p -> TyFV p -> TyFV p
fvsKiVarBndr var fvs = delFV (In3 var) fvs

fvsOfTypes :: [Type p] -> TyFV p
fvsOfTypes [] fv_cand in_scope acc = emptyFV fv_cand in_scope acc
fvsOfTypes (ty:tys) fv_cand in_scope acc
  = (fvsOfType ty `unionFV` fvsOfTypes tys) fv_cand in_scope acc

varsOfTypeDSet :: Type p -> (DTyVarSet p, DKiCoVarSet p, DKiVarSet p)
varsOfTypeDSet ty = case fvVarAcc (fvsOfType ty) of
  (tvs, _, kcvs, _, kvs, _) -> (mkDVarSet tvs, mkDVarSet kcvs, mkDVarSet kvs)

varsOfTypeList :: Type p -> ([TyVar p], [KiCoVar p], [KiVar p])
varsOfTypeList ty = case fvVarAcc (fvsOfType ty) of
  (tvs, _, kcvs, _, kvs, _) -> (tvs, kcvs, kvs)

varsOfTypesList :: [Type p] -> ([TyVar p], [KiCoVar p], [KiVar p])
varsOfTypesList tys = case fvVarAcc (fvsOfTypes tys) of
  (tvs, _, kcvs, _, kvs, _) -> (tvs, kcvs, kvs)

typeSomeFreeVars
  :: (E3 (TyVar p) (KiCoVar p) (KiVar p) -> Bool)
  -> Type p
  -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
typeSomeFreeVars fv_cand ty = case fvVarAcc (filterFV fv_cand $ fvsOfType ty) of
  (_, tvs, _, kcvs, _, kvs) -> (tvs, kcvs, kvs)

{- *********************************************************************
*                                                                      *
            Injective free vars
*                                                                      *
********************************************************************* -}

isInjectiveInType :: TyVar p -> Type p -> Bool
isInjectiveInType tv ty = go ty
  where
    go ty | Just ty' <- rewriterView ty = go ty'
    go (TyVarTy tv') = tv' == tv
    go (AppTy f a) = go f || go a
    go (FunTy _ ty1 ty2) = go ty1 || go ty2
    go (TyConApp tc tys) = go_tc tc tys
    go (ForAllTy (Bndr tv' _) ty) = tv /= tv' && go ty
    go (ForAllKiCo _ ty) = go ty
    go (CastTy ty _) = go ty
    go KindCoercion{} = False
    go Embed{} = False
    go (TyLamTy tv' ty) = tv /= tv' && go ty
    go (BigTyLamTy _ ty) = go ty
    

    go_tc tc tys = any go tys

{- *********************************************************************
*                                                                      *
            Any free vars
*                                                                      *
********************************************************************* -}

afvFolder
  :: (TyVar p -> Bool) -> (KiCoVar p -> Bool) -> (KiVar p -> Bool)
  -> TyCoFolder p
     (TyVarSet p, KiCoVarSet p, KiVarSet p)
     (KiCoVarSet p, KiVarSet p)
     DM.Any DM.Any
afvFolder f_tv f_kcv f_kv = TyCoFolder { tcf_view = noView
                                       , tcf_tyvar = do_tyvar
                                       , tcf_covar = panic "afvFolder do_covar"
                                       , tcf_hole = panic "do_hole"
                                       , tcf_tybinder = do_bndr
                                       , tcf_kcobinder = do_bndr_kco
                                       , tcf_tylambinder = do_tylambndr
                                       , tcf_tylamkibinder = do_kilambndr
                                       , tcf_swapEnv = \(_, kcv, kv) -> (kcv, kv)
                                       , tcf_embedKiRes = id
                                       , tcf_mkcf = mafvFolder f_kcv f_kv }
  where
    do_tyvar (is, _, _) tv = Any (not (tv `elemVarSet` is) && f_tv tv)
    do_bndr (is, kcvs, kvs) tv _
      = (is `extendVarSet` tv, kcvs, kvs)
    do_bndr_kco (is, kcvs, kvs) kcv
      = (is, kcvs `extendVarSet` kcv, kvs)
    do_tylambndr (is, kcvs, kvs) tv
      = (is `extendVarSet` tv, kcvs, kvs)
    do_kilambndr (tv, kcv, is) kv = (tv, kcv, is `extendVarSet` kv)

noFreeVarsOfType :: Type p -> Bool
noFreeVarsOfType ty = not $ DM.getAny (f ty)
  where (f, _, _, _) = foldTyCo (afvFolder (const True) (const True) (const True))
                 (emptyVarSet, emptyVarSet, emptyVarSet)

{- *********************************************************************
*                                                                      *
            Free type constructors
*                                                                      *
********************************************************************* -}

tyConsOfType :: Type p -> UniqSet (TyCon p)
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

tyConsOfTypes :: [Type p] -> UniqSet (TyCon p)
tyConsOfTypes tys = foldr (unionUniqSets . tyConsOfType) emptyUniqSet tys
