module CSlash.Core.Type.Ppr where

-- import {-# SOURCE #-} CSlash.Types.Var (TypeVar)
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import CSlash.Utils.Outputable (Outputable, SDoc)
import {-# SOURCE #-} CSlash.Types.Var (VarHasKind)

pprType :: VarHasKind tv kv => Type tv kv -> SDoc

pprTyVar :: VarHasKind tv kv => tv -> SDoc
