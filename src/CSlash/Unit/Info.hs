module CSlash.Unit.Info
  ( GenericUnitInfo(..)
  , GenUnitInfo
  , UnitInfo

  , PackageId(..)
  , PackageName(..)
  , Version(..)
  ) where

import CSlash.Platform.Ways

import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import CSlash.Types.Unique

import CSlash.Data.FastString
-- import qualified GHC.Data.ShortText as ST

import CSlash.Unit.Module as Module
-- import CSlash.Unit.Ppr
import CSlash.Unit.Database

import CSlash.Settings

import Data.Version
import Data.Bifunctor
import Data.List (isPrefixOf, stripPrefix)

type GenUnitInfo unit
  = GenericUnitInfo PackageId PackageName unit ModuleName (GenModule (GenUnit unit))

type UnitInfo = GenUnitInfo UnitId

newtype PackageId = PackageId FastString deriving (Eq)

newtype PackageName = PackageName
  { unPackageName :: FastString }
  deriving (Eq)

instance Uniquable PackageId where
  getUnique (PackageId n) = getUnique n

instance Uniquable PackageName where
  getUnique (PackageName n) = getUnique n

instance Outputable PackageId where
  ppr (PackageId str) = ftext str

instance Outputable PackageName where
  ppr (PackageName str) = ftext str
