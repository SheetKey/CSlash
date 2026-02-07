module CSlash.Core.Type where

import CSlash.Cs.Pass

import {-# SOURCE #-} CSlash.Core.TyCon
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Kind (Kind, KindCoercion)
import CSlash.Types.Name (Name)
import CSlash.Types.Basic (Arity)
import CSlash.Utils.Misc (HasDebugCallStack)

rewriterView :: HasPass p pass => Type p -> Maybe (Type p)

coreView :: HasPass p pass => Type p -> Maybe (Type p)

mkAppTy :: Type p -> Type p -> Type p

mkTyConApp :: TyCon p -> [Type p] -> Type p

mkCastTy :: HasPass p pass => Type p -> KindCoercion p -> Type p

buildSynTyCon :: Name -> Kind Zk -> Arity -> Type Zk -> TyCon p

typeKind :: (HasDebugCallStack, HasPass p pass) => Type p -> Kind p
