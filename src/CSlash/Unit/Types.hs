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
import CSlash.Utils.Outputable

import Data.Data

data GenModule unit = Module
  { moduleUnit :: !unit
  , moduleName :: !ModuleName
  }
  deriving (Eq, Ord, Data, Functor)

type Module = GenModule Unit

instance Outputable Module where
  ppr = pprModule

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

unitUnique :: IsUnitId u => GenUnit u -> Unique
unitUnique (VirtUnit x) = instUnitKey x
unitUnique (RealUnit (Definite x)) = getUnique (unitFS x)
unitUnique HoleUnit = holeUnique

fsToUnit :: FastString -> Unit
fsToUnit = RealUnit . Definite . UnitId

unitString :: IsUnitId u => u -> String
unitString = unpackFS . unitFS

newtype Definite unit = Definite { unDefinite :: unit }
  deriving (Functor)

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

mainUnitId :: UnitId
mainUnitId = UnitId (fsLit "main")

mainUnit :: Unit
mainUnit = RealUnit (Definite mainUnitId)
