module CSlash.Core.DataCon where

import {-# SOURCE #-} CSlash.Types.Var (Id, TypeVar)
import {-# SOURCE #-} CSlash.Types.Name (Name, NamedThing)
import CSlash.Types.Unique (Uniquable)
import CSlash.Utils.Outputable (Outputable, OutputableBndr)
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)

data DataCon

dataConName :: DataCon -> Name
dataConWorkId :: DataCon -> Id

instance Eq DataCon
instance Uniquable DataCon
instance NamedThing DataCon
instance Outputable DataCon
instance OutputableBndr DataCon

dataConFullSig :: DataCon -> ([TypeVar],[Type], Type)
