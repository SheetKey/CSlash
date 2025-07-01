module CSlash.Core.Kind where

import CSlash.Utils.Outputable 
import {-# SOURCE #-} CSlash.Types.Var (AsGenericKi)

data Kind kv
data MonoKind kv
data KindCoercion kv
type PredKind = MonoKind

instance Outputable kv => Outputable (Kind kv)
instance Outputable kv => Outputable (MonoKind kv)
instance AsGenericKi Kind 
instance AsGenericKi MonoKind 

pprKind :: Outputable kv => Kind kv -> SDoc

isCoVarKind :: MonoKind kv -> Bool
isKiEvVarKind :: MonoKind kv -> Bool