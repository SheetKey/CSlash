{-# LANGUAGE LambdaCase #-}
module CSlash.Types.TyThing where

import CSlash.Cs.Pass

import CSlash.Types.GREInfo
import CSlash.Types.Name
import CSlash.Types.Name.Reader
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Unique.Set

import CSlash.Core.DataCon
import CSlash.Core.ConLike
import CSlash.Core.TyCon

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic

data TyThing p
  = AnId (Id p)
  | AConLike (ConLike p)
  | ATyCon (TyCon p)

-- Wire-in TyThing 
type WITyThing = TyThing Zk

instance Outputable (TyThing p) where
  ppr = pprShortTyThing

instance NamedThing (TyThing p) where
  getName (AnId id) = getName id
  getName (ATyCon tc) = getName tc
  getName (AConLike cl) = conLikeName cl

mkATyCon :: TyCon p -> TyThing p
mkATyCon = ATyCon

mkAnId :: Id p -> TyThing p
mkAnId = AnId

pprShortTyThing :: TyThing p -> SDoc
pprShortTyThing = undefined

tyThingCategory :: TyThing p -> String
tyThingCategory (ATyCon _) = "type constructor"
tyThingCategory (AnId _) = "identifier"
tyThingCategory (AConLike (RealDataCon _)) = "data constructor"
tyThingCategory (AConLike PatSynCon) = "pattern synonym"

implicitTyConThings :: TyCon p -> [TyThing Zk]
implicitTyConThings tc
  = datacon_stuff
  where
    --datacon_stuff :: [TyThing Zk]
    datacon_stuff = [ty_thing | dc <- cons
                              , ty_thing <- [ AConLike (RealDataCon dc)
                                            , dataConImplicitTyThing dc] ]
    --cons :: [DataCon Zk]
    cons = tyConDataCons tc

tyThingGREInfo :: TyThing p -> GREInfo
tyThingGREInfo = \case
  AConLike con -> IAmConLike $ conLikeConInfo con
  AnId _ -> Vanilla
  ATyCon tc -> IAmTyCon $ tyConFlavor tc
