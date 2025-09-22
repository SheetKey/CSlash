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

data TyThing tv kv
  = AnId (Id tv kv)
  | AConLike (ConLike tv kv)
  | ATyCon (TyCon tv kv)

-- Wire-in TyThing
type WITyThing = TyThing (TyVar KiVar) KiVar

instance AsAnyTy TyThing where
  asAnyTyKi (AnId id) = AnId $ asAnyTyKi id
  asAnyTyKi (AConLike cl) = AConLike $ asAnyTyKi cl
  asAnyTyKi (ATyCon tc) = ATyCon $ asAnyTyKi tc

instance (Outputable tv, Outputable kv) => Outputable (TyThing tv kv) where
  ppr = pprShortTyThing

instance NamedThing (TyThing tv kv) where
  getName (AnId id) = getName id
  getName (ATyCon tc) = getName tc
  getName (AConLike cl) = conLikeName cl

mkATyCon :: TyCon tv kv -> TyThing tv kv
mkATyCon = ATyCon

mkAnId :: Id tv kv -> TyThing tv kv
mkAnId = AnId

pprShortTyThing :: (Outputable tv, Outputable kv) => TyThing tv kv -> SDoc
pprShortTyThing = undefined

tyThingCategory :: TyThing tv kv -> String
tyThingCategory (ATyCon _) = "type constructor"
tyThingCategory (AnId _) = "identifier"
tyThingCategory (AConLike (RealDataCon _)) = "data constructor"
tyThingCategory (AConLike PatSynCon) = "pattern synonym"

implicitTyConThings :: TyCon tv kv -> [TyThing (TyVar KiVar) KiVar]
implicitTyConThings tc
  = datacon_stuff
  where
    --datacon_stuff :: [TyThing tv kv]
    datacon_stuff = [ty_thing | dc <- cons
                              , ty_thing <- [ AConLike (RealDataCon dc)
                                            , dataConImplicitTyThing dc] ]
    --cons :: [DataCon]
    cons = tyConDataCons tc

tyThingGREInfo :: TyThing tv kv -> GREInfo
tyThingGREInfo = \case
  AConLike con -> IAmConLike $ conLikeConInfo con
  AnId _ -> Vanilla
  ATyCon tc -> IAmTyCon $ tyConFlavor tc
