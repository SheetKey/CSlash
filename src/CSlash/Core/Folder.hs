{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Folder where

import CSlash.Core.Rep
-- import CSlash.Core.Type
-- import CSlash.Core.Kind

import CSlash.Types.Var

import CSlash.Utils.Panic

data CoreFolder p env a = CoreFolder
  { cf_ty_view :: Type p -> Maybe (Type p)
  , cf_fa_kv :: env -> KiVar p -> env
  , cf_fa_kcv :: env -> KiCoVar p -> env
  , cf_fa_tv :: env -> TyVar p -> ForAllFlag -> env
  , cf_lam_kv :: env -> KiVar p -> env
  , cf_lam_tv :: env -> TyVar p -> env
  , cf_kv :: env -> KiVar p -> a
  , cf_kcv :: env -> KiCoVar p -> a
  , cf_tv :: env -> TyVar p -> a
  , cf_tcv :: env -> TyCoVar p -> a
  , cf_thole :: env -> TypeCoercionHole -> a
  , cf_khole :: env -> KindCoercionHole -> a
  }

{-# INLINE foldCore #-}
foldCore
  :: Monoid a
  => CoreFolder p env a
  -> env
  -> ( Type p -> a, [Type p] -> a
     , TypeCoercion p -> a, [TypeCoercion p] -> a
     , MonoKind p -> a, [MonoKind p] -> a
     , Kind p -> a, [Kind p] -> a
     , KindCoercion p -> a, [KindCoercion p] -> a )
foldCore CoreFolder{..} env
  = ( go_ty env, go_tys env
    , go_tco env, go_tcos env
    , go_mki env, go_mkis env
    , go_ki env, go_kis env
    , go_kco env, go_kcos env )
  where
    go_tys _ [] = mempty
    go_tys env (t:ts) = go_ty env t `mappend` go_tys env ts

    go_tcos _ [] = mempty
    go_tcos env (c:cs) = go_tco env c `mappend` go_tcos env cs

    go_mkis _ [] = mempty
    go_mkis env (k:ks) = go_mki env k `mappend` go_mkis env ks

    go_kis _ [] = mempty
    go_kis env (k:ks) = go_ki env k `mappend` go_kis env ks

    go_kcos _ [] = mempty
    go_kcos env (c:cs) = go_kco env c `mappend` go_kcos env cs

    go_set_rows _ [] = mempty
    go_set_rows env (r:rs) = go_set_row env r `mappend` go_set_rows env rs

    go_ty env ty | Just ty' <- cf_ty_view ty = go_ty env ty'
    go_ty env (TyVarTy tv) = cf_tv env tv
    go_ty env (AppTy t1 t2) = go_ty env t1 `mappend` go_ty env t2
    go_ty env (TyLamTy tv ty)
      = let !env' = cf_lam_tv env tv
        in go_mki env (varKind tv) `mappend`
           go_ty env' ty
    go_ty env (BigTyLamTy kv ty)
      = let !env' = cf_lam_kv env kv
        in go_ty env' ty
    go_ty env (FunTy mki arg res)
      = go_mki env mki `mappend`
        go_ty env arg `mappend`
        go_ty env res
    go_ty env (TyConApp _ tys) = go_tys env tys
    go_ty env (ForAllTy (Bndr tv vis) ty)
      = let !env' = cf_fa_tv env tv vis
        in go_mki env (varKind tv) `mappend`
           go_ty env' ty
    go_ty env (ForAllKiCo kcv ty)
      = let !env' = cf_fa_kcv env kcv
        in go_mki env (varKind kcv) `mappend`
           go_ty env' ty
    go_ty env (Embed mki) = go_mki env mki
    go_ty env (CastTy ty kco)
      = go_ty env ty `mappend` go_kco env kco
    go_ty env (KindCoercion kco) = go_kco env kco
    go_ty env (LocalTyRow nm ki) = go_mki env ki
    go_ty env (SetRowsTy ty rows) = go_ty env ty `mappend` go_set_rows env rows

    go_set_row env (SetRowVal nm e ty) = panic "Folder go_set_row setrowval"
    go_set_row env (SetRowTy _ ty) = go_ty env ty

    go_tco env (TyRefl ty) = go_ty env ty
    go_tco env (AppCo c1 c2) = go_tco env c1 `mappend` go_tco env c2
    go_tco env (TyCoVarCo cv) = cf_tcv env cv
    go_tco env (TyHoleCo hole) = cf_thole env hole
    go_tco env (TySymCo co) = go_tco env co
    go_tco env (TyTransCo c1 c2) = go_tco env c1 `mappend` go_tco env c2
    go_tco env (LRCo _ co) = go_tco env co
    go_tco env (LiftKCo kco) = go_kco env kco
    go_tco env (TyFunCo kco c1 c2)
      = go_kco env kco `mappend` go_tco env c1 `mappend` go_tco env c2
    go_tco env (ForAllCo tv f _ kco co)
      = let !env' = cf_fa_tv env tv f
        in go_kco env kco `mappend`
           go_mki env (varKind tv) `mappend`
           go_tco env' co
    go_tco env (ForAllCoCo kcv kco co)
      = let !env' = cf_fa_kcv env kcv
        in go_kco env kco `mappend`
           go_mki env (varKind kcv) `mappend`
           go_tco env' co

    go_ki env (Mono mki) = go_mki env mki
    go_ki env (ForAllKi kv ki)
      = let !env' = cf_fa_kv env kv
        in go_ki env' ki

    go_mki env (KiVarKi kv) = cf_kv env kv
    go_mki env (BIKi _) = mempty
    go_mki env (FunKi _ arg res)
      = go_mki env arg `mappend` go_mki env res
    go_mki env (KiPredApp _ k1 k2)
      = go_mki env k1 `mappend` go_mki env k2
    go_mki env (KiConApp (KiCon _ base rows))
      = go_mki env base `mappend` go_row_sigs env rows

    go_row_sigs _ [] = mempty
    go_row_sigs env (r:rs) = go_row_sig env r `mappend` go_row_sigs env rs

    go_row_sig env (RowTySig _ ty) = go_ty env ty
    go_row_sig env (RowKiSig _ ki) = go_mki env ki

    go_kco env (Refl ki) = go_mki env ki
    go_kco env BI_U_A = mempty
    go_kco env BI_A_L = mempty
    go_kco env (BI_U_LTEQ ki) = go_mki env ki
    go_kco env (BI_LTEQ_L ki) = go_mki env ki
    go_kco env (LiftEq co) = go_kco env co
    go_kco env (LiftLT co) = go_kco env co
    go_kco env (HoleCo hole) = cf_khole env hole
    go_kco env (FunCo _ _ c1 c2)
      = go_kco env c1 `mappend` go_kco env c2
    go_kco env (SelCo _ co) = go_kco env co
    go_kco env (KiCoVarCo cv) = cf_kcv env cv
    go_kco env (SymCo co) = go_kco env co
    go_kco env (TransCo c1 c2) = go_kco env c1 `mappend` go_kco env c2

