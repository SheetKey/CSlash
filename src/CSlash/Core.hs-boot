{-# LANGUAGE RoleAnnotations #-}

module CSlash.Core where

import CSlash.Cs.Pass
import {-# SOURCE #-} CSlash.Types.Var

data Expr a b

type CoreBndr = CoreBndrP Zk
type role CoreBndrP nominal
data CoreBndrP p

type CoreExpr = Expr CoreBndr CoreId

type CoreId = Id Zk
-- type CoreType = Type Zk
-- type CoreKind = Kind Zk
-- type CoreMonoKind = MonoKind Zk
-- type CoreVarSets = (IdSet Zk, TyVarSet Zk, KiCoVarSet Zk, KiVarSet Zk)

data Unfolding

noUnfolding :: Unfolding

evaldUnfolding :: Unfolding

isEvaldUnfolding :: Unfolding -> Bool
