module CSlash.Core where

data Expr a

type CoreBndr = Var

type CoreExpr = Expr CoreBndr