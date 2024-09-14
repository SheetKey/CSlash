module CSlash.Types.TyThing where

import {-# SOURCE #-} CSlash.Core.TyCon
import {-# SOURCE #-} CSlash.Types.Var

data TyThing

mkATyCon :: TyCon -> TyThing

mkAnId :: Id -> TyThing