module CSlash.Types.Id.Info where

import CSlash.Utils.Outputable (SDoc)
import {-# SOURCE #-} CSlash.Types.Var (AsAnyTy)

data IdInfo
data IdDetails tv kv

pprIdDetails :: IdDetails tv kv -> SDoc

instance AsAnyTy IdDetails