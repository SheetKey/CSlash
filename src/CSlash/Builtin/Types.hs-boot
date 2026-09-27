{-# LANGUAGE FlexibleContexts #-}

module CSlash.Builtin.Types where

import CSlash.Cs.Pass

import {-# SOURCE #-} CSlash.Core.TyCon (TyCon)
import {-# SOURCE #-} CSlash.Core.DataCon (DataCon)

import CSlash.Types.Basic (Arity, ConTag)
import {-# SOURCE #-} CSlash.Types.Name (Name)
import {-# SOURCE #-} CSlash.Types.Var (TyVar, KiVar)

tupleTyConName :: Arity -> Name
tupleDataConName :: Arity -> Name

tupleDataCon :: Arity -> DataCon Zk
tupleTyCon :: Arity -> TyCon p

sumDataCon :: ConTag -> Arity -> DataCon Zk
sumTyCon :: Arity -> TyCon p
