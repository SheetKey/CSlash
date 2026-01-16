module CSlash.Types.Id.Info where

import CSlash.Utils.Outputable (SDoc)
import {-# SOURCE #-} CSlash.Types.Var (AsAnyTy)

data IdInfo
data IdDetails

pprIdDetails :: IdDetails -> SDoc
