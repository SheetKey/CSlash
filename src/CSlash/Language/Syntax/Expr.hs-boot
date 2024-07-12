{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE KindSignatures #-}

module CSlash.Language.Syntax.Expr where

import Data.Kind (Type)

type role MatchGroup nominal nominal
data MatchGroup (p :: Type) (b :: Type)
