module CSlash.Core.Type where

import CSlash.Cs.Pass

import {-# SOURCE #-} CSlash.Core.TyCon
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Kind (Kind, KindCoercion)
import CSlash.Types.Name (Name)
import CSlash.Types.Basic (Arity)
import CSlash.Utils.Misc (HasDebugCallStack)

rewriterView :: Type p -> Maybe (Type p)

coreView :: Type p -> Maybe (Type p)

mkAppTy :: Type p -> Type p -> Type p

mkTyConApp :: TyCon p -> [Type p] -> Type p

mkCastTy :: Type p -> KindCoercion p -> Type p

buildSynTyCon
  :: Name -> Kind Zk -> Arity -> Type Zk -> TyCon p

typeKind :: HasDebugCallStack => Type p -> Kind p
