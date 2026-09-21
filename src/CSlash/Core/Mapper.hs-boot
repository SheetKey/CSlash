{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}

module CSlash.Core.Mapper where

import {-# SOURCE #-} CSlash.Core.Rep
import CSlash.Core.TyCon

import CSlash.Cs.Pass

import CSlash.Types.Var
  
data CoreMapper p p' env (m :: * -> *) = CoreMapper
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
