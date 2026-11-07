{-# LANGUAGE RoleAnnotations #-}

module CSlash.Types.TyThing where

import {-# SOURCE #-} CSlash.Core.TyCon
import {-# SOURCE #-} CSlash.Types.Var.Id
import {-# SOURCE #-} CSlash.Types.Var.KiVar
import {-# SOURCE #-} CSlash.Core.Rep
import CSlash.Cs.Pass

type role TyThing nominal
data TyThing p
type WITyThing = TyThing Zk

mkATyCon :: TyCon p -> TyThing p

mkAKiCon :: ([KiVar p], KiCon p) -> TyThing p

aRow :: TyThing p

mkAnId :: Id p -> TyThing p