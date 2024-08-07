{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RoleAnnotations #-}
{-# LANGUAGE KindSignatures #-}

module CSlash.Language.Syntax.Expr where

import CSlash.Language.Syntax.Extension (XRec)
import Data.Kind (Type)

type role CsExpr nominal
type role MatchGroup nominal nominal
type role GRHSs nominal nominal
data CsExpr (i :: Type)
data MatchGroup (p :: Type) (b :: Type)
data GRHSs (a :: Type) (body :: Type)
type family SyntaxExpr (i :: Type)

type LCsExpr a = XRec a (CsExpr a)
