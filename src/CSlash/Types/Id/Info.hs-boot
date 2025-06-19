module CSlash.Types.Id.Info where

import CSlash.Utils.Outputable (SDoc)

data IdInfo
data IdDetails tv kv

pprIdDetails :: IdDetails tv kv -> SDoc
