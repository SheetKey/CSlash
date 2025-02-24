module CSlash.Types.Id.Make where

import CSlash.Types.Name (Name)
import CSlash.Types.Var (Id)
import {-# SOURCE #-} CSlash.Core.DataCon (DataCon)

mkDataConId :: Name -> DataCon -> Id
