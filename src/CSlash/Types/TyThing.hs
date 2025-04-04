{-# LANGUAGE LambdaCase #-}
module CSlash.Types.TyThing where

import CSlash.Types.GREInfo
import CSlash.Types.Name
import CSlash.Types.Name.Reader
import CSlash.Types.Var
import CSlash.Types.Id
import CSlash.Types.Id.Info
import CSlash.Types.Unique.Set

import CSlash.Core.DataCon
import CSlash.Core.ConLike
import CSlash.Core.TyCon

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic

data TyThing
  = AnId Id
  | AConLike ConLike
  | ATyCon TyCon

instance Outputable TyThing where
  ppr = pprShortTyThing

instance NamedThing TyThing where
  getName (AnId id) = getName id
  getName (ATyCon tc) = getName tc
  getName (AConLike cl) = conLikeName cl

mkATyCon :: TyCon -> TyThing
mkATyCon = ATyCon

mkAnId :: Id -> TyThing
mkAnId = AnId

pprShortTyThing = undefined

tyThingCategory :: TyThing -> String
tyThingCategory (ATyCon _) = "type constructor"
tyThingCategory (AnId _) = "identifier"
tyThingCategory (AConLike (RealDataCon _)) = "data constructor"
tyThingCategory (AConLike PatSynCon) = "pattern synonym"

implicitTyConThings :: TyCon -> [TyThing]
implicitTyConThings tc
  = datacon_stuff
  where
    datacon_stuff :: [TyThing]
    datacon_stuff = [ty_thing | dc <- cons
                              , ty_thing <- [ AConLike (RealDataCon dc)
                                            , dataConImplicitTyThing dc] ]
    cons :: [DataCon]
    cons = tyConDataCons tc

tyThingGREInfo :: TyThing -> GREInfo
tyThingGREInfo = \case
  AConLike con -> IAmConLike $ conLikeConInfo con
  AnId _ -> Vanilla
  ATyCon tc -> IAmTyCon (fmap tyConName $ tyConFlavor tc)               
