module CSlash.Builtin.Types where

import {-# SOURCE #-} CSlash.Core.TyCon (TyCon)
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Kind (Kind)
import {-# SOURCE #-} CSlash.Core.DataCon (DataCon)

import CSlash.Types.Basic (Arity, ConTag)
import {-# SOURCE #-} CSlash.Types.Name (Name)
import {-# SOURCE #-} CSlash.Types.Var (TyVar, KiVar)

tupleTyConName :: Arity -> Name
tupleDataConName :: Arity -> Name

tupleDataCon :: Arity -> DataCon (TyVar KiVar) KiVar
tupleTyCon :: Arity -> TyCon (TyVar KiVar) KiVar

sumDataCon :: ConTag -> Arity -> DataCon (TyVar KiVar) KiVar
sumTyCon :: Arity -> TyCon (TyVar KiVar) KiVar
