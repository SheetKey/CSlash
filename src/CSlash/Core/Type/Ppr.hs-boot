module CSlash.Core.Type.Ppr where

import CSlash.Cs.Pass

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import CSlash.Utils.Outputable (Outputable, SDoc)
import {-# SOURCE #-} CSlash.Types.Var (TyVar)

pprType :: HasPass p pass => Type p -> SDoc

pprTyVar :: TyVar p -> SDoc
