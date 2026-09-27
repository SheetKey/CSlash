module CSlash.Core.Folder where

import {-# SOURCE #-} CSlash.Core.Rep
-- import CSlash.Core.Type
-- import CSlash.Core.Kind

import CSlash.Types.Var

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

foldCore
  :: Monoid a
  => CoreFolder p env a
  -> env
  -> ( Type p -> a, [Type p] -> a
     , TypeCoercion p -> a, [TypeCoercion p] -> a
     , MonoKind p -> a, [MonoKind p] -> a
     , Kind p -> a, [Kind p] -> a
     , KindCoercion p -> a, [KindCoercion p] -> a )
