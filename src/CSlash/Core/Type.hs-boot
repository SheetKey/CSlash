module CSlash.Core.Type where

import {-# SOURCE #-} CSlash.Core.TyCon
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Kind (Kind, KindCoercion)
import CSlash.Types.Var (TyVar, KiVar, IsTyVar)
import CSlash.Types.Name (Name)
import CSlash.Types.Basic (Arity)
import CSlash.Utils.Misc (HasDebugCallStack)

rewriterView :: IsTyVar tv kv => Type tv kv -> Maybe (Type tv kv)

coreView :: IsTyVar tv kv => Type tv kv -> Maybe (Type tv kv)

mkAppTy :: Type tv kv -> Type tv kv -> Type tv kv

mkTyConApp :: TyCon tv kv -> [Type tv kv] -> Type tv kv

mkCastTy :: IsTyVar tv kv => Type tv kv -> KindCoercion kv -> Type tv kv

buildSynTyCon
  :: Name -> Kind KiVar -> Arity -> Type (TyVar KiVar) KiVar -> TyCon (TyVar KiVar) KiVar

typeKind :: (HasDebugCallStack, IsTyVar tv kv) => Type tv kv -> Kind kv
