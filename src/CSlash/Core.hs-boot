module CSlash.Core where

import CSlash.Cs.Pass
import {-# SOURCE #-} CSlash.Types.Var

data Expr a

type CoreBndr = Id Zk

type CoreExpr = Expr CoreBndr

data Unfolding

noUnfolding :: Unfolding

evaldUnfolding :: Unfolding

isEvaldUnfolding :: Unfolding -> Bool
