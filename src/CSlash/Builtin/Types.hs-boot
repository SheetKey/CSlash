module CSlash.Builtin.Types where

import {-# SOURCE #-} CSlash.Core.TyCon (TyCon)
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import {-# SOURCE #-} CSlash.Core.Kind (Kind)
import {-# SOURCE #-} CSlash.Core.DataCon (DataCon)

import CSlash.Types.Basic (Arity, ConTag)
import {-# SOURCE #-} CSlash.Types.Name (Name)

tupleTyConName :: Arity -> Name
tupleDataConName :: Arity -> Name

tupleDataCon :: Arity -> DataCon tv kv
tupleTyCon :: Arity -> TyCon tv kv

sumDataCon :: ConTag -> Arity -> DataCon tv kv
sumTyCon :: Arity -> TyCon tv kv
