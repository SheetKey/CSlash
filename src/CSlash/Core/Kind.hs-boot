{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RoleAnnotations #-}

module CSlash.Core.Kind where

import CSlash.Cs.Pass

import CSlash.Utils.Outputable 
import Data.Data (Data)

type role Kind nominal
data Kind p

type role MonoKind nominal
data MonoKind kv

type role KindCoercion nominal
data KindCoercion kv

type PredKind = MonoKind

data FunKiFlag

instance IsPass p => Outputable (Kind (CsPass p))
instance IsPass p => Outputable (MonoKind (CsPass p))
instance Data p => Data (MonoKind p)
instance Data FunKiFlag
instance Outputable FunKiFlag

pprKind :: HasPass p pass => Kind p -> SDoc

isKiCoVarKind :: MonoKind p -> Bool
