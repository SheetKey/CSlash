module CSlash.Types.TyThing where

import {-# SOURCE #-} CSlash.Core.TyCon
import {-# SOURCE #-} CSlash.Types.Var

data TyThing tv kv
type WITyThing = TyThing (TyVar KiVar) KiVar

mkATyCon :: TyCon tv kv -> TyThing tv kv

mkAnId :: Id tv kv -> TyThing tv kv