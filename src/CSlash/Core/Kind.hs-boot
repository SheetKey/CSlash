module CSlash.Core.Kind where

import CSlash.Utils.Outputable 
import {-# SOURCE #-} CSlash.Types.Var (AsGenericKi, AsAnyKi)
import Data.Data (Data)

data Kind kv
data MonoKind kv
data KindCoercion kv
type PredKind = MonoKind
data FunKiFlag

instance Outputable kv => Outputable (Kind kv)
instance Outputable kv => Outputable (MonoKind kv)
instance AsGenericKi Kind 
instance AsGenericKi MonoKind 
instance AsAnyKi MonoKind
instance (Data kv) => Data (MonoKind kv)
instance Data FunKiFlag
instance Outputable FunKiFlag

pprKind :: Outputable kv => Kind kv -> SDoc

isKiCoVarKind :: MonoKind kv -> Bool
