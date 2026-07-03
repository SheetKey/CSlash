module CSlash.Builtin.Utils where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Builtin.Uniques
-- import GHC.Builtin.PrimOps
-- import GHC.Builtin.PrimOps.Ids
import CSlash.Builtin.Types
-- import GHC.Builtin.Types.Literals ( typeNatTyCons )
import CSlash.Builtin.Types.Prim
-- import GHC.Builtin.Names.TH ( templateHaskellNames )
import CSlash.Builtin.Names

import CSlash.Core.ConLike ( ConLike(..) )
import CSlash.Core.DataCon
-- import GHC.Core.Class
import CSlash.Core.TyCon

import CSlash.Types.Avail
import CSlash.Types.Var (TyVar, KiVar, varName)
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Make
import CSlash.Types.Name hiding (varName)
import CSlash.Types.Name.Env
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Map
import CSlash.Types.TyThing
import CSlash.Types.Unique ( isValidKnownKeyUnique, pprUniqueAlways )

import CSlash.Utils.Outputable
import CSlash.Utils.Misc as Utils
import CSlash.Utils.Panic
import CSlash.Utils.Constants (debugIsOn)
-- import GHC.Hs.Doc
import CSlash.Unit.Module.ModIface (IfaceExport)

import CSlash.Data.List.SetOps

import Control.Applicative ((<|>))
import Data.List        ( find )
import Data.Maybe
import Data.Array (elems)

import Debug.Trace (trace)

knownKeyNames :: [Name]
knownKeyNames
  | debugIsOn
  , Just badNamesDoc <- knownKeyNamesOkay all_names
  = pprPanic "badAllKnownKeyNames" badNamesDoc
  | otherwise
  = all_names
  where
    all_names =
      concat [ concatMap wired_tycon_kk_names primTyCons
             , concatMap wired_tycon_kk_names wiredInTyCons
             , map varName wiredInIds
             , basicKnownKeyNames
             ]
    wired_tycon_kk_names :: TyCon Zk -> [Name]
    wired_tycon_kk_names tc = tyConName tc : implicits
      where implicits = concatMap thing_kk_names (implicitTyConThings tc)

    wired_datacon_kk_names :: DataCon Zk -> [Name]
    wired_datacon_kk_names dc = [dataConName dc]

    thing_kk_names :: TyThing Zk -> [Name]
    thing_kk_names (ATyCon tc) = wired_tycon_kk_names tc
    thing_kk_names (AConLike (RealDataCon dc)) = wired_datacon_kk_names dc
    thing_kk_names thing = [getName thing]

knownKeyNamesOkay :: [Name] -> Maybe SDoc
knownKeyNamesOkay all_names
  | ns@(_:_) <- filter (not . isValidKnownKeyUnique . getUnique) all_names
  = Just $ text "    Out-of-range known-key uniques: " <>
           brackets (pprWithCommas (ppr . nameOccName) ns)
  | null badNamesPairs
  = Nothing
  | otherwise
  = Just badNamesDoc
  where
    namesEnv = foldl' (\m n -> extendNameEnv_Acc (:) Utils.singleton m n n)
                      emptyUFM all_names
    badNamesEnv = filterNameEnv (\ns -> ns `lengthExceeds` 1) namesEnv
    badNamesPairs = nonDetUFMToList badNamesEnv

    badNamesDoc :: SDoc
    badNamesDoc = vcat $ map pairToDoc badNamesPairs

    pairToDoc :: (Unique, [Name]) -> SDoc
    pairToDoc (uniq, ns) = text "        " <>
                           pprUniqueAlways uniq <>
                           text ": " <>
                           brackets (pprWithCommas (ppr . nameOccName) ns)

lookupKnownKeyName :: Unique -> Maybe Name
lookupKnownKeyName u =
  knownUniqueName u <|> lookupUFM_Directly knownKeysMap u

isKnownKeyName :: Name -> Bool
isKnownKeyName n =
  isJust (knownUniqueName $ nameUnique n) || elemUFM n knownKeysMap

knownKeysMap :: UniqFM Name Name
knownKeysMap = listToIdentityUFM knownKeyNames

{- *********************************************************************
*                                                                      *
            Export lists for pseudo-modules (CSL.Prim and CSL.BuiltIn)
*                                                                      *
********************************************************************* -}

{- NOTE: Our goal:
CSL.BuiltIn is a module auto imported to every .cs file.
It exports things we always want available:
tuples/sums (builtin syntax)
Bool, IO

CSL.Prim exports built-in things we don't always want:
primitive functions used to implement higher level apis.
Note that 'Prim' module does not correspond to 'PrimTyCon's (which may be BuiltIn)
-}

cslPrimExports :: [IfaceExport]
cslPrimExports
  = map (Avail . varName) csPrimIds ++
    [ AvailTC n [n]
    | tc <- primPrimTyCons
    , let n = tyConName tc ]

cslBuiltInExports :: [IfaceExport]
cslBuiltInExports
  = [ AvailTC n [n]
    | tc <- builtInPrimTyCons
    , let n = tyConName tc ] ++
    [ AvailTC n (n : (dataConName <$> tyConDataCons tc))
    | tc <- wiredInTyCons
    , let n = tyConName tc ]
    
