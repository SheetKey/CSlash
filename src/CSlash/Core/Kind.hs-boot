module CSlash.Core.Kind where

import CSlash.Utils.Outputable 

data Kind

instance Outputable Kind

pprKind :: Kind -> SDoc
