module CSlash.Types.TyThing where

import CSlash.Types.GREInfo
import CSlash.Types.Name
import CSlash.Types.Name.Reader
import CSlash.Types.Var
import CSlash.Types.Id
import CSlash.Types.Id.Info
import CSlash.Types.Unique.Set

import CSlash.Core.DataCon
import CSlash.Core.TyCon

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic

data TyThing
  = AnId Id
  | ADataCon DataCon
  | ATyCon TyCon

instance Outputable TyThing where
  ppr = pprShortTyThing

instance NamedThing TyThing where
  getName (AnId id) = getName id
  getName (ADataCon dc) = getName dc
  getName (ATyCon tc) = getName tc

mkATyCon :: TyCon -> TyThing
mkATyCon = ATyCon

mkAnId :: Id -> TyThing
mkAnId = AnId

pprShortTyThing = undefined
