{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RoleAnnotations #-}

module CSlash.Core.Rep where

import {-# SOURCE #-} CSlash.Core.TyCon (TyCon)
import {-# SOURCE #-} CSlash.Types.Var.KiVar (KiVar)

import CSlash.Cs.Pass
import CSlash.Utils.Outputable 
import Data.Data (Data)

type role Type nominal
data Type tv 

type role TypeCoercion nominal
data TypeCoercion p

data TypeCoercionHole

type role Kind nominal
data Kind p
  = ForAllKi !(KiVar p) (Kind p)
  | Mono (MonoKind p)

type role MonoKind nominal
data MonoKind p

type role KindCoercion nominal
data KindCoercion kv

data KindCoercionHole

data FunKiFlag

instance IsPass p => Outputable (Type (CsPass p))
instance IsPass p => Outputable (Kind (CsPass p))
instance IsPass p => Outputable (MonoKind (CsPass p))
instance Data p => Data (MonoKind p)
instance Data FunKiFlag
instance Outputable FunKiFlag

mkNakedTyConTy :: TyCon p -> Type p
