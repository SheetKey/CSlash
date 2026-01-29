{-# LANGUAGE RoleAnnotations #-}

module CSlash.Core.Kind where

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

instance Outputable (Kind p)
instance Outputable (MonoKind p)
instance Data p => Data (MonoKind p)
instance Data FunKiFlag
instance Outputable FunKiFlag

pprKind :: Kind p -> SDoc

isKiCoVarKind :: MonoKind p -> Bool
