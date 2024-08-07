module CSlash.Core.Type.Ppr where

import {-# SOURCE #-} CSlash.Types.Var (TypeVar)
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import CSlash.Utils.Outputable (SDoc)

pprType :: Type -> SDoc

pprTyVar :: TypeVar -> SDoc
