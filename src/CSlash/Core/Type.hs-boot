module CSlash.Core.Type where

import {-# SOURCE #-} CSlash.Core.TyCon
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)

mkAppTy :: Type -> Type -> Type

mkTyConApp :: TyCon -> [Type] -> Type
