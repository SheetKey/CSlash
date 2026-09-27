{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Mapper where

import CSlash.Cs.Pass

import CSlash.Core.Rep
import CSlash.Core.TyCon
import CSlash.Core.Type 
import CSlash.Core.Kind

import CSlash.Types.Var

import CSlash.Utils.Panic

data CoreMapper p p' env m = CoreMapper
  { cm_kv :: env -> KiVar p -> m (MonoKind p')
  , cm_kcv :: env -> KiCoVar p -> m (KindCoercion p')
  , cm_tv :: env -> TyVar p -> m (Type p')
  , cm_tcv :: env -> TyCoVar p -> m (TypeCoercion p')
  , cm_khole :: env -> KindCoercionHole -> m (KindCoercion p')
  , cm_thole :: env -> TypeCoercionHole -> m (TypeCoercion p')
  , cm_lam_kv :: forall r. env -> KiVar p -> (env -> KiVar p' -> m r) -> m r
  , cm_lam_tv :: forall r. env -> TyVar p -> (env -> TyVar p' -> m r) -> m r
  , cm_fa_kv :: forall r. env -> KiVar p -> (env -> KiVar p' -> m r) -> m r
  , cm_fa_kcv :: forall r. env -> KiCoVar p -> (env -> KiCoVar p' -> m r) -> m r
  , cm_fa_tv :: forall r. env -> TyVar p -> ForAllFlag -> (env -> TyVar p' -> m r) -> m r
  , cm_tycon :: TyCon p -> m (TyCon p')
  }

{-# INLINE mapCore #-}
mapCore
  :: (Monad m, HasPass p' pass')
  => CoreMapper p p' () m
  -> ( Type p -> m (Type p')
     , [Type p] -> m [Type p']
     , TypeCoercion p -> m (TypeCoercion p')
     , [TypeCoercion p] -> m [TypeCoercion p']
     , MonoKind p -> m (MonoKind p')
     , [MonoKind p] -> m [MonoKind p']
     , Kind p -> m (Kind p')
     , [Kind p] -> m [Kind p']
     , KindCoercion p -> m (KindCoercion p')
     , [KindCoercion p] -> m [KindCoercion p'] )
mapCore mapper = case mapCoreX mapper of
  ( go_ty, go_tys, 
    go_tco, go_tcos,
    go_mki, go_mkis,
    go_ki, go_kis,
    go_kco, go_kcos )
    -> ( go_ty (), go_tys ()
       , go_tco (), go_tcos ()
       , go_mki (), go_mkis ()
       , go_ki (), go_kis ()
       , go_kco (), go_kcos () )
         
{-# INLINE mapCoreX #-}
mapCoreX
  :: (Monad m, HasPass p' pass')
  => CoreMapper p p' env m
  -> ( env -> Type p -> m (Type p')
     , env -> [Type p] -> m [Type p']
     , env -> TypeCoercion p -> m (TypeCoercion p')
     , env -> [TypeCoercion p] -> m [TypeCoercion p']
     , env -> MonoKind p -> m (MonoKind p')
     , env -> [MonoKind p] -> m [MonoKind p']
     , env -> Kind p -> m (Kind p')
     , env -> [Kind p] -> m [Kind p']
     , env -> KindCoercion p -> m (KindCoercion p')
     , env -> [KindCoercion p] -> m [KindCoercion p'] )
mapCoreX CoreMapper{..}
  = ( go_ty, go_tys, go_tco, go_tcos
    , go_mki, go_mkis, go_ki, go_kis, go_kco, go_kcos )
  where
    go_tys !_ [] = return []
    go_tys !env (x:xs) = (:) <$> go_ty env x <*> go_tys env xs

    go_tcos !_ [] = return []
    go_tcos !env (x:xs) = (:) <$> go_tco env x <*> go_tcos env xs
    
    go_mkis !_ [] = return []
    go_mkis !env (x:xs) = (:) <$> go_mki env x <*> go_mkis env xs
    
    go_kis !_ [] = return []
    go_kis !env (x:xs) = (:) <$> go_ki env x <*> go_kis env xs

    go_kcos !_ [] = return []
    go_kcos !env (x:xs) = (:) <$> go_kco env x <*> go_kcos env xs
    
    go_set_rows !_ [] = return []
    go_set_rows !env (r:rs) = (:) <$> go_set_row env r <*> go_set_rows env rs

    go_row_sigs !_ [] = return []
    go_row_sigs !env (r:rs) = (:) <$> go_row_sig env r <*> go_row_sigs env rs

    go_ty !env (TyVarTy tv) = cm_tv env tv
    go_ty !env (AppTy t1 t2) = mkAppTy <$> go_ty env t1 <*> go_ty env t2
    go_ty !env ty@(FunTy ki arg res) = do
      ki' <- go_mki env ki
      arg' <- go_ty env arg
      res' <- go_ty env res
      return $ FunTy ki' arg' res'
    go_ty !env ty@(TyConApp tc tys) = do
      tc' <- cm_tycon tc
      mkTyConApp tc' <$> go_tys env tys
    go_ty !env (ForAllTy (Bndr tv vis) inner) =
      cm_fa_tv env tv vis $ \env' tv' -> do
      inner' <- go_ty env' inner
      return $ ForAllTy (Bndr tv' vis) inner'
    go_ty !env (ForAllKiCo kcv inner) =
      cm_fa_kcv env kcv $ \env' kcv' -> do
      inner' <- go_ty env' inner
      return $ ForAllKiCo kcv' inner'
    go_ty !env (TyLamTy tv inner) =
      cm_lam_tv env tv $ \env' tv' -> do
      inner' <- go_ty env' inner
      return $ TyLamTy tv' inner'
    go_ty !env (BigTyLamTy kv inner) =
      cm_lam_kv env kv $ \env' kv' -> do
      inner' <- go_ty env' inner
      return $ BigTyLamTy kv' inner'
    go_ty !env (Embed ki) = Embed <$> go_mki env ki
    go_ty !env (CastTy ty kco) = mkCastTy <$> go_ty env ty <*> go_kco env kco
    go_ty !env (KindCoercion kco) = KindCoercion <$> go_kco env kco
    go_ty !env (LocalTyRow nm ki) = LocalTyRow nm <$> go_mki env ki
    go_ty !env (SetRowsTy ty rs) = SetRowsTy <$> go_ty env ty <*> go_set_rows env rs

    go_set_row !env (SetRowVal nm _ _) = return $ panic "SetRowVal nm"
    go_set_row !env (SetRowTy nm ty) = SetRowTy nm <$> go_ty env ty

    go_tco !env (TyRefl ty) = TyRefl <$> go_ty env ty
    go_tco !env (GRefl ty kco) = mkGReflCo <$> go_ty env ty <*> go_kco env kco
    go_tco !env (AppCo c1 c2) = mkAppCo <$> go_tco env c1 <*> go_tco env c2
    go_tco !env (TyFunCo kco c1 c2)
      = mkTyFunCo <$> go_kco env kco <*> go_tco env c1 <*> go_tco env c2
    go_tco !env (TyCoVarCo cv) = cm_tcv env cv
    go_tco !env (TyHoleCo hole) = cm_thole env hole
    go_tco !env (TySymCo co) = mkSymTyCo <$> go_tco env co
    go_tco !env (TyTransCo c1 c2) = mkTyTransCo <$> go_tco env c1 <*> go_tco env c2
    go_tco !env (LRCo lr co) = mkLRTyCo lr <$> go_tco env co
    go_tco !env (LiftKCo kco) = LiftKCo <$> go_kco env kco
    go_tco !env (TyConAppCo tc cos) = do
      tc' <- cm_tycon tc
      mkTyConAppCo tc' <$> go_tcos env cos
    go_tco !env (ForAllCo tv visL visR kco tco) = do
      kco' <- go_kco env kco
      cm_fa_tv env tv visL $ \env' tv' -> do
        tco' <- go_tco env tco
        return $ mkForAllCo tv' visL visR kco' tco'
    go_tco !env (ForAllCoCo kcv kco tco) = do
      kco' <- go_kco env kco
      cm_fa_kcv env kcv $ \env' kcv' -> do
        tco' <- go_tco env' tco
        return $ mkForAllCoCo kcv' kco' tco'

    go_ki !env (Mono ki) = Mono <$> go_mki env ki
    go_ki !env (ForAllKi kv ki) =
      cm_fa_kv env kv $ \env' kv' -> ForAllKi kv' <$> go_ki env' ki

    go_mki !env (KiVarKi kv) = cm_kv env kv
    go_mki !env (BIKi b) = return $ BIKi b
    go_mki !env (KiConApp (KiCon nm base rows)) = do
      base' <- go_mki env base
      rows' <- go_row_sigs env rows
      return $ KiConApp $ KiCon nm base' rows'
    go_mki !env (KiPredApp pred ki1 ki2)
      = mkKiPredApp pred <$> go_mki env ki1 <*> go_mki env ki2
    go_mki !env (FunKi fl arg res) =
      FunKi fl <$> go_mki env arg <*> go_mki env res

    go_row_sig !env (RowTySig nm ty) = RowTySig nm <$> go_ty env ty
    go_row_sig !env (RowKiSig nm ki) = RowKiSig nm <$> go_mki env ki

    go_kco !env (Refl ki) = Refl <$> go_mki env ki
    go_kco !env BI_U_A = return BI_U_A
    go_kco !env BI_A_L = return BI_A_L
    go_kco !env (BI_U_LTEQ ki) = BI_U_LTEQ <$> go_mki env ki
    go_kco !env (BI_LTEQ_L ki) = BI_LTEQ_L <$> go_mki env ki
    go_kco !env (LiftEq co) = LiftEq <$> go_kco env co
    go_kco !env (LiftLT co) = LiftLT <$> go_kco env co
    go_kco !env (FunCo afl afr c1 c2)
      = mkFunKiCo2 afl afr <$> go_kco env c1 <*> go_kco env c2
    go_kco !env (KiCoVarCo cv) = cm_kcv env cv
    go_kco !env (HoleCo hole) = cm_khole env hole
    go_kco !env (SymCo co) = mkSymKiCo <$> go_kco env co
    go_kco !env (TransCo c1 c2) = mkTransKiCo <$> go_kco env c1 <*> go_kco env c2
    go_kco !env (SelCo i co) = mkSelCo i <$> go_kco env co
