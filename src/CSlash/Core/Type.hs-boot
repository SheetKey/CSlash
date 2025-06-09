module CSlash.Core.Type where

import {-# SOURCE #-} CSlash.Core.TyCon
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Kind (KindCoercion)
import CSlash.Types.Var (VarHasKind)

coreView :: VarHasKind tv kv => Type tv kv -> Maybe (Type tv kv)

mkAppTy :: Type tv kv -> Type tv kv -> Type tv kv

mkTyConApp :: TyCon tv kv -> [Type tv kv] -> Type tv kv

mkCastTy :: VarHasKind tv kv => Type tv kv -> KindCoercion tv kv -> Type tv kv
