module CSlash.Core.DataCon where

import {-# SOURCE #-} CSlash.Types.Var (Id, AsAnyTy)
import {-# SOURCE #-} CSlash.Types.Name (Name, NamedThing)
import CSlash.Types.Unique (Uniquable)
import CSlash.Utils.Outputable (Outputable, OutputableBndr)
import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import CSlash.Types.Basic (Arity)

data DataCon tv kv

dataConName :: DataCon tv kv -> Name
dataConId :: DataCon tv kv -> Id tv kv

instance Eq (DataCon tv kv)
instance Uniquable (DataCon tv kv)
instance NamedThing (DataCon tv kv)
instance Outputable (DataCon tv kv)
instance OutputableBndr (DataCon tv kv)
instance AsAnyTy DataCon

dataConFullSig :: DataCon tv kv -> Type tv kv
dataConArity :: DataCon tv kv -> Arity
