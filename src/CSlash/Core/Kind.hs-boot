module CSlash.Core.Kind where

import CSlash.Utils.Outputable 

data Kind kv
data MonoKind kv
data KindCoercion kv kcv

instance Outputable kv => Outputable (Kind kv)
instance Outputable kv => Outputable (MonoKind kv)

pprKind :: Outputable kv => Kind kv -> SDoc

isCoVarKind :: MonoKind kv -> Bool