module CSlash.Unit.State
  ( module CSlash.Unit.Info
  , module CSlash.Unit.State
  ) where

import CSlash.Driver.DynFlags

import CSlash.Platform
import CSlash.Platform.Ways

-- import GHC.Unit.Database
import CSlash.Unit.Info
-- import GHC.Unit.Ppr
import CSlash.Unit.Types
import CSlash.Unit.Module
import CSlash.Unit.Home

import CSlash.Types.Unique.FM
import CSlash.Types.Unique.DFM
import CSlash.Types.Unique.Set
import CSlash.Types.Unique.DSet
import CSlash.Types.Unique.Map
import CSlash.Types.Unique
import CSlash.Types.PkgQual

import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Outputable as Outputable
import CSlash.Data.Maybe

import System.Environment ( getEnv )
import CSlash.Data.FastString
-- import qualified GHC.Data.ShortText as ST
import CSlash.Utils.Logger
import CSlash.Utils.Error
import CSlash.Utils.Exception

import System.Directory
import System.FilePath as FilePath
import Control.Monad
import Data.Graph (stronglyConnComp, SCC(..))
import Data.Char ( toUpper )
import Data.List ( intersperse, partition, sortBy, isSuffixOf, sortOn )
import Data.Set (Set)
import Data.Monoid (First(..))
import qualified Data.Semigroup as Semigroup
import qualified Data.Set as Set
-- import GHC.LanguageExtensions
import Control.Applicative

data ModuleOrigin
  = ModHidden
  | ModUnusable !UnusableUnit
  | ModOrigin
    { fromOrigUnit :: Maybe Bool
    , fromExposedReexport :: [UnitInfo]
    , fromHiddenReexport :: [UnitInfo]
    , fromPackageFlag :: Bool
    }

data UnusableUnit = UnusableUnit
  { uuUnit :: !Unit
  , uuReason :: !UnusableUnitReason
  , uuIsReexport :: !Bool
  }
  

type PreloadUnitClosure = UniqSet UnitId

type ModuleNameProvidersMap = UniqMap ModuleName (UniqMap Module ModuleOrigin)

data UnitState = UnitState
  { unitInfoMap :: UnitInfoMap
  , preloadClosure :: PreloadUnitClosure
  , packageNameMap :: UniqFM PackageName UnitId
  , wireMap :: UniqMap UnitId UnitId
  , unwireMap :: UniqMap UnitId UnitId
  , preloadUnits :: [UnitId]
  , explicitUnits :: [(Unit, Maybe PackageArg)]
  , homeUnitDepends :: [UnitId]
  , moduleNameProvidersMap :: !ModuleNameProvidersMap
  , requirementContext :: UniqMap ModuleName [InstantiatedModule]
  , allowVirtualUnits :: !Bool
  }

data UnitDatabase unit = UnitDatbase
  { unitDatabasePath :: FilePath
  , unitDatabaseUnits :: [GenUnitInfo unit]
  }

type UnitInfoMap = UniqMap UnitId UnitInfo

data UnusableUnitReason
  = IgnoredWithFlag
  | BrokenDependencies [UnitId]
  | CyclicDependencies [UnitId]
  | IgnoredDependencies [UnitId]
  | ShadowedDependencies [UnitId]

-- -----------------------------------------------------------------------------
-- Displaying packages

pprUnits :: UnitState -> SDoc
pprUnit = pprUnitsWith pprUnitInfo

pprUnitsWith :: (UnitInfo -> SDoc) -> UnitState -> SDoc
pprUnitsWith pprIPI pkgstate =
  vcat (intersperse (text "---") (map pprIPI (listUnitInfo pkgstate)))
