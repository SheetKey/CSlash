{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CSlash.Unit.Types where

import Prelude hiding ((<>))

import CSlash.Language.Syntax.Module.Name

import CSlash.Data.FastString
import CSlash.Types.Unique
import CSlash.Types.Unique.DSet
import CSlash.Utils.Encoding
import CSlash.Utils.Fingerprint
import CSlash.Utils.Outputable
import CSlash.Utils.Misc

import Control.DeepSeq
import Data.Data
import Data.List (sortBy)
import Data.Function
import Data.Bifunctor
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS.Char8

data GenModule unit = Module
  { moduleUnit :: !unit
  , moduleName :: !ModuleName
  }
  deriving (Eq, Ord, Data, Functor)

type Module = GenModule Unit

moduleUnitId :: Module -> UnitId
moduleUnitId = toUnitId . moduleUnit

type InstalledModule = GenModule UnitId

type HomeUnitModule = GenModule UnitId

type InstantiatedModule = GenModule InstantiatedUnit

mkModule :: u -> ModuleName -> GenModule u
mkModule = Module

instance NFData (GenModule a) where
  rnf (Module unit name) = unit `seq` name `seq` ()

instance Outputable Module where
  ppr = pprModule

instance Outputable InstalledModule where
  ppr (Module p n) = ppr p <> char ':' <> pprModuleName n

instance Outputable InstantiatedUnit where
  ppr = pprInstantiatedUnit

pprInstantiatedUnit :: InstantiatedUnit -> SDoc
pprInstantiatedUnit uid =
    pprUnitId cid <>
      (if not (null insts)
        then
         brackets (hcat
                   (punctuate comma $
                    [ pprModuleName modname <> text "=" <> pprModule m
                    | (modname, m) <- insts]))
       else empty)
  where
    cid = instUnitInstanceOf uid
    insts = instUnitInsts uid

class IsUnitId u where
  unitFS :: u -> FastString

instance IsUnitId UnitId where
  unitFS (UnitId fs) = fs

instance IsUnitId u => IsUnitId (GenUnit u) where
  unitFS (VirtUnit x) = instUnitFS x
  unitFS (RealUnit (Definite x)) = unitFS x
  unitFS HoleUnit = holeFS

pprModule :: IsLine doc => Module -> doc
pprModule mod@(Module p n) = docWithStyle code doc
  where
    code = (if p == mainUnit
             then empty
             else ztext (zEncodeFS (unitFS p)) <> char '_')
           <> pprModuleName n
    doc sty
      | qualModule sty mod =
          case p of
            HoleUnit -> angleBrackets (pprModuleName n)
            _ -> pprUnit p <> char ':' <> pprModuleName n
      | otherwise = pprModuleName n
{-# SPECIALIZE pprModule :: Module -> SDoc #-}
{-# SPECIALIZE pprModule :: Module -> HLine #-}

data GenUnit uid
  = RealUnit !(Definite uid)
  | VirtUnit {-# UNPACK #-} !(GenInstantiatedUnit uid)
  | HoleUnit

data GenInstantiatedUnit unit = InstantiatedUnit
  { instUnitFS :: !FastString
  , instUnitKey :: !Unique
  , instUnitInstanceOf :: !unit
  , instUnitInsts :: !(GenInstantiations unit)
  , instUnitHoles :: UniqDSet ModuleName
  }

type Unit = GenUnit UnitId

type InstantiatedUnit = GenInstantiatedUnit UnitId

type GenInstantiations unit = [(ModuleName, GenModule (GenUnit unit))]

holeUnique :: Unique
holeUnique = getUnique holeFS

holeFS :: FastString
holeFS = fsLit "<hole>"

instance Eq (GenInstantiatedUnit unit) where
  u1 == u2 = instUnitKey u1 == instUnitKey u2

instance Ord (GenInstantiatedUnit unit) where
  u1 `compare` u2 = instUnitFS u1 `lexicalCompareFS` instUnitFS u2

instance IsUnitId u => Eq (GenUnit u) where
  uid1 == uid2 = unitUnique uid1 == unitUnique uid2

instance IsUnitId u => Uniquable (GenUnit u) where
  getUnique = unitUnique

instance Ord Unit where
  nm1 `compare` nm2 = stableUnitCmp nm1 nm2

instance Data Unit where
  toConstr _ = abstractConstr "Unit"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "Unit"

stableUnitCmp :: Unit -> Unit -> Ordering
stableUnitCmp p1 p2 = unitFS p1 `lexicalCompareFS` unitFS p2

instance Outputable Unit where
  ppr pk = pprUnit pk

pprUnit :: Unit -> SDoc
pprUnit (RealUnit (Definite d)) = pprUnitId d
pprUnit (VirtUnit uid) = pprInstantiatedUnit uid
pprUnit HoleUnit = ftext holeFS

instance Show Unit where
  show = unitString

unitFreeModuleHoles :: GenUnit u -> UniqDSet ModuleName
unitFreeModuleHoles (VirtUnit x) = instUnitHoles x
unitFreeModuleHoles (RealUnit _) = emptyUniqDSet
unitFreeModuleHoles HoleUnit = emptyUniqDSet

moduleFreeHoles :: GenModule (GenUnit u) -> UniqDSet ModuleName
moduleFreeHoles (Module HoleUnit name) = unitUniqDSet name
moduleFreeHoles (Module u _) = unitFreeModuleHoles u

mkInstantiatedUnit :: IsUnitId u => u -> GenInstantiations u -> GenInstantiatedUnit u
mkInstantiatedUnit cid insts =
  InstantiatedUnit
  { instUnitInstanceOf = cid
  , instUnitInsts = sorted_insts
  , instUnitHoles = unionManyUniqDSets (map (moduleFreeHoles.snd) insts)
  , instUnitFS = fs
  , instUnitKey = getUnique fs
  }
  where
    fs = mkInstantiatedUnitHash cid sorted_insts
    sorted_insts = sortBy (stableModuleNameCmp `on` fst) insts

mkVirtUnit :: IsUnitId u => u -> [(ModuleName, GenModule (GenUnit u))] -> GenUnit u
mkVirtUnit uid [] = RealUnit $ Definite uid
mkVirtUnit uid insts = VirtUnit $ mkInstantiatedUnit uid insts

mkInstantiatedUnitHash
  :: IsUnitId u => u
  -> [(ModuleName, GenModule (GenUnit u))]
  -> FastString
mkInstantiatedUnitHash cid sorted_holes =
    mkFastStringByteString
  . fingerprintUnitId (bytesFS (unitFS cid))
  $ hashInstantiations sorted_holes

hashInstantiations :: IsUnitId u => [(ModuleName, GenModule (GenUnit u))] -> Fingerprint
hashInstantiations sorted_holes =
    fingerprintByteString
  . BS.concat $ do
      (m, b) <- sorted_holes
      [ bytesFS (moduleNameFS m), BS.Char8.singleton ' ',
        bytesFS (unitFS (moduleUnit b)), BS.Char8.singleton ':',
        bytesFS (moduleNameFS (moduleName b)), BS.Char8.singleton '\n']

fingerprintUnitId :: BS.ByteString -> Fingerprint -> BS.ByteString
fingerprintUnitId prefix (Fingerprint a b)
  = BS.concat
  $ [ prefix
    , BS.Char8.singleton '-'
    , BS.Char8.pack (toBase62Padded a)
    , BS.Char8.pack (toBase62Padded b)
    ]

unitUnique :: IsUnitId u => GenUnit u -> Unique
unitUnique (VirtUnit x) = instUnitKey x
unitUnique (RealUnit (Definite x)) = getUnique (unitFS x)
unitUnique HoleUnit = holeUnique

fsToUnit :: FastString -> Unit
fsToUnit = RealUnit . Definite . UnitId

unitString :: IsUnitId u => u -> String
unitString = unpackFS . unitFS

stringToUnit :: String -> Unit
stringToUnit = fsToUnit . mkFastString

mapGenUnit :: IsUnitId v => (u -> v) -> GenUnit u -> GenUnit v
mapGenUnit f = go
  where
    go gu = case gu of
      HoleUnit -> HoleUnit
      RealUnit d -> RealUnit (fmap f d)
      VirtUnit i ->
        VirtUnit $ mkInstantiatedUnit
            (f (instUnitInstanceOf i))
            (fmap (second (fmap go)) (instUnitInsts i))

mapInstantiations
  :: IsUnitId v => (u -> v)
  -> GenInstantiations u
  -> GenInstantiations v
mapInstantiations f = map (second (fmap (mapGenUnit f)))

toUnitId :: Unit -> UnitId
toUnitId (RealUnit (Definite iuid)) = iuid
toUnitId (VirtUnit indef) = instUnitInstanceOf indef
toUnitId HoleUnit = error "Hole unit"

stringToUnitId :: String -> UnitId
stringToUnitId = UnitId . mkFastString

newtype Definite unit = Definite { unDefinite :: unit }
  deriving (Functor)

virtualUnitId :: InstantiatedUnit -> UnitId
virtualUnitId i = UnitId (instUnitFS i)

newtype UnitId = UnitId { unitIdFS :: FastString }
  deriving (Data)

instance Eq UnitId where
  uid1 == uid2 = getUnique uid1 == getUnique uid2

instance Ord UnitId where
  u1 `compare` u2 = unitIdFS u1 `lexicalCompareFS` unitIdFS u2

instance Uniquable UnitId where
  getUnique = getUnique . unitIdFS

instance Outputable UnitId where
  ppr = pprUnitId

pprUnitId :: UnitId -> SDoc
pprUnitId (UnitId fs) = sdocOption sdocUnitIdForUser ($ fs)

primUnitId :: UnitId
primUnitId = UnitId (fsLit "cslash-prim")

primUnit :: Unit
primUnit = RealUnit (Definite primUnitId)

mainUnitId :: UnitId
mainUnitId = UnitId (fsLit "main")

mainUnit :: Unit
mainUnit = RealUnit (Definite mainUnitId)
