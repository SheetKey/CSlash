{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RoleAnnotations #-}

module CSlash.Core.Kind where

import {-# SOURCE #-} CSlash.Core.Rep
import CSlash.Types.Var.KiVar

class SKC kind where
  mkKiVarKi :: KiVar p -> kind p
  mkKiVarKis :: [KiVar p] -> [kind p]
  mkKiVarKis = map mkKiVarKi

instance SKC MonoKind

instance SKC Kind 

class SKG kind where
  getKiVar_maybe :: kind p -> Maybe (KiVar p)

instance SKG Kind 
instance SKG MonoKind 
{-
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
-}