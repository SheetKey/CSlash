{-# LANGUAGE RoleAnnotations #-}

module CSlash.Types.TyThing where

import {-# SOURCE #-} CSlash.Core.TyCon
import {-# SOURCE #-} CSlash.Types.Var.Id
import CSlash.Cs.Pass

type role TyThing nominal
data TyThing p
type WITyThing = TyThing Zk

mkATyCon :: TyCon p -> TyThing p

mkAnId :: Id p -> TyThing p