module CSlash.Unit.Types where

import CSlash.Language.Syntax.Module.Name

import CSlash.Data.FastString
import CSlash.Types.Unique
import CSlash.Types.Unique.DSet

data GenModule unit = Module
  { moduleUnit :: !unit
  , moduleName :: !ModuleName
  }
  deriving (Eq, Ord, Data, Functor)

type Module = GenModule Unit

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

type GenInstantiations unit = [(ModuleName, GenModule (GenUnit unit))]

newtype Definite unit = Definite { unDefinite :: unit }
  deriving (Functor)

newtype UnitId = UnitId { unitIdFS :: FastString }
  deriving (Data)
