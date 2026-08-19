{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RoleAnnotations #-}

module CSlash.Core.Type.Rep where

import {-# SOURCE #-} CSlash.Core.TyCon (TyCon)

import CSlash.Cs.Pass

import CSlash.Utils.Outputable (Outputable)

import qualified Data.Data as Data

type role Type nominal
data Type tv 

instance Data.Data tv => Data.Data (Type tv)

type PredType = Type

mkNakedTyConTy :: TyCon p -> Type p

instance IsPass p => Outputable (Type (CsPass p))

type role TypeCoercion nominal
data TypeCoercion p 

instance Data.Typeable p => Data.Data (TypeCoercion p)

isReflTyCo :: TypeCoercion p -> Bool
isReflTyCo_maybe :: HasPass p pass => TypeCoercion p -> Maybe (Type p)
