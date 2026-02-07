{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RoleAnnotations #-}

module CSlash.Core.Type.Rep where

import {-# SOURCE #-} CSlash.Core.TyCon (TyCon)

import CSlash.Cs.Pass

import CSlash.Utils.Outputable (Outputable)

type role Type nominal
data Type tv 

type PredType = Type

mkNakedTyConTy :: TyCon p -> Type p

instance IsPass p => Outputable (Type (CsPass p))