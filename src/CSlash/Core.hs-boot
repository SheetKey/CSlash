{-# LANGUAGE RoleAnnotations #-}

module CSlash.Core where

import CSlash.Cs.Pass
import {-# SOURCE #-} CSlash.Types.Var

data Expr a

type role CoreBndr nominal
data CoreBndr p

type CoreExpr = Expr (CoreBndr Zk)

data Unfolding

noUnfolding :: Unfolding

evaldUnfolding :: Unfolding

isEvaldUnfolding :: Unfolding -> Bool
