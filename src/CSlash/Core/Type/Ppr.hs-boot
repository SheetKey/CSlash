module CSlash.Core.Type.Ppr where

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import CSlash.Utils.Outputable (Outputable, SDoc)
import {-# SOURCE #-} CSlash.Types.Var (TyVar)

pprType :: Type p -> SDoc

pprTyVar :: TyVar p -> SDoc
