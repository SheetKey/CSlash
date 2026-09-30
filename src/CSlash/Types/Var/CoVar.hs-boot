{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE KindSignatures #-}

module CSlash.Types.Var.CoVar where

import {-# SOURCE #-} CSlash.Core.Rep (MonoKind)

type role CoVar representational nominal
data CoVar (thing :: * -> *) p
type KiCoVar = CoVar MonoKind
