module CSlash.Types.Name (
    module CSlash.Types.Name,
    module CSlash.Types.Name.Occurrence
) where

import {-# SOURCE #-} CSlash.Types.Name.Occurrence
import CSlash.Types.Unique
import CSlash.Utils.Outputable
import Data.Data (Data)
import Control.DeepSeq (NFData)

data Name

instance Eq Name
instance Data Name
instance Uniquable Name
instance Outputable Name
instance NFData Name

class NamedThing a where
    getOccName :: a -> OccName
    getName    :: a -> Name

    getOccName n = nameOccName (getName n)

nameUnique :: Name -> Unique
setNameUnique :: Name -> Unique -> Name
nameOccName :: Name -> OccName
tidyNameOcc :: Name -> OccName -> Name
