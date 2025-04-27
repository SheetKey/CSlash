module CSlash.Core.Kind where

import CSlash.Utils.Outputable 

data Kind
data MonoKind

instance Outputable Kind
instance Outputable MonoKind

pprKind :: Kind -> SDoc
