{-# LANGUAGE RoleAnnotations #-}

module CSlash.Core.DataCon where

import CSlash.Cs.Pass

import {-# SOURCE #-} CSlash.Types.Var.Id (Id)
import {-# SOURCE #-} CSlash.Types.Name (Name, NamedThing)
import CSlash.Types.Unique (Uniquable)
import CSlash.Utils.Outputable (Outputable, OutputableBndr)
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import CSlash.Types.Basic (Arity)

type role DataCon phantom
data DataCon p

dataConName :: DataCon p -> Name
dataConId :: DataCon p -> Id Zk

instance Eq (DataCon p)
instance Uniquable (DataCon p)
instance NamedThing (DataCon p)
instance Outputable (DataCon p)
instance OutputableBndr (DataCon p)

dataConFullSig :: DataCon p -> Type Zk
dataConArity :: DataCon p -> Arity
