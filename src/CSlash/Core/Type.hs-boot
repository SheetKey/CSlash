module CSlash.Core.Type where

import {-# SOURCE #-} CSlash.Core.TyCon
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Kind (KindCoercion)

coreView :: Type tv kv -> Maybe (Type tv kv)

mkAppTy :: Type tv kv -> Type tv kv -> Type tv kv

mkTyConApp :: TyCon tv kv -> [Type tv kv] -> Type tv kv

mkCastTy :: Type tv kv -> KindCoercion tv kv -> Type tv kv
