module CSlash.Core where

import {-# SOURCE #-} CSlash.Types.Var

data Expr a

type CoreBndr = Var

type CoreExpr = Expr CoreBndr