module CSlash.Core.Type.Ppr where

-- import {-# SOURCE #-} CSlash.Types.Var (TypeVar)
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import CSlash.Utils.Outputable (Outputable, SDoc)

pprType :: (Outputable tv, Outputable kv) => Type tv kv -> SDoc

pprTyVar :: Outputable tv => tv -> SDoc
