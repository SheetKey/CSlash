module CSlash.Types.Id.Make where

import CSlash.Types.Name (Name)
import CSlash.Types.Var (Id, TyVar, KiVar)
import {-# SOURCE #-} CSlash.Core.DataCon (DataCon)

mkDataConId :: Name -> DataCon (TyVar KiVar) KiVar -> Id (TyVar KiVar) KiVar
