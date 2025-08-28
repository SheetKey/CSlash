module CSlash.Core where

import {-# SOURCE #-} CSlash.Types.Var

data Expr a

type CoreBndr = Id (TyVar KiVar) KiVar

type CoreExpr = Expr CoreBndr