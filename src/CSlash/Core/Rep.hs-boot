{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RoleAnnotations #-}

module CSlash.Core.Rep where

import {-# SOURCE #-} CSlash.Core.TyCon (TyCon)
import {-# SOURCE #-} CSlash.Types.Var.KiVar (KiVar)

import CSlash.Cs.Pass
-- import CSlash.Cs.Extension
import CSlash.Utils.Outputable 
import Data.Data (Data)

type KnotTied ty = ty

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

instance HasPass p p' => Outputable (Type (CsPass p'))
instance HasPass p p' => Outputable (Kind (CsPass p'))
instance HasPass p p' => Outputable (MonoKind (CsPass p'))
instance Data p => Data (MonoKind p)
instance Data FunKiFlag
instance Outputable FunKiFlag

mkNakedTyConTy :: TyCon p -> Type p

mkTyConApp :: TyCon p -> [Type p] -> Type p
