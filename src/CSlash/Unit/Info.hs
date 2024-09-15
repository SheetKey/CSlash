{-# LANGUAGE RecordWildCards #-}

module CSlash.Unit.Info
  ( GenericUnitInfo(..)
  , GenUnitInfo
  , UnitInfo

  , mkUnit

  , PackageId(..)
  , PackageName(..)
  , Version(..)
  , pprUnitInfo
  ) where

import Prelude hiding ((<>))

import CSlash.Platform.Ways

import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import CSlash.Types.Unique

import CSlash.Data.FastString
import qualified GHC.Data.ShortText as ST

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

pprUnitInfo :: UnitInfo -> SDoc
pprUnitInfo GenericUnitInfo {..} =
  vcat [ field "name" (ppr unitPackageName)
       , field "version" (text (showVersion unitPackageVersion))
       , field "id" (ppr unitId)
       , field "exposed" (ppr unitIsExposed)
       , field "exposed-modules" (ppr unitExposedModules)
       , field "hidden-modules" (fsep (map ppr unitHiddenModules))
       , field "import-dirs" (fsep (map (text . ST.unpack) unitImportDirs))
       , field "library-dirs" (fsep (map (text . ST.unpack) unitLibraryDirs))
       , field "dynamic-library-dirs" (fsep (map (text . ST.unpack) unitLibraryDynDirs))
       , field "hs-libraries" (fsep (map (text . ST.unpack) unitLibraries))
       , field "extra-libraries" (fsep (map (text . ST.unpack) unitExtDepLibsSys))
       , field "include-dirs" (fsep (map (text . ST.unpack) unitIncludeDirs))
       , field "includes" (fsep (map (text . ST.unpack) unitIncludes))
       , field "depends" (fsep (map ppr  unitDepends))
       , field "ld-options" (fsep (map (text . ST.unpack) unitLinkerOptions))
       ]
  where
    field name body = text name <> colon <+> nest 4 body

mkUnit :: UnitInfo -> Unit
mkUnit p
  | unitIsIndefinite p = mkVirtUnit (unitInstanceOf p) (unitInstantiations p)
  | otherwise = RealUnit (Definite (unitId p))
