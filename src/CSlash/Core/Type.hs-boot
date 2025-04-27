module CSlash.Core.Type where

import {-# SOURCE #-} CSlash.Core.TyCon
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Kind (KindCoercion)

coreView :: Type -> Maybe Type

mkAppTy :: Type -> Type -> Type

mkTyConApp :: TyCon -> [Type] -> Type

mkCastTy :: Type -> KindCoercion -> Type
