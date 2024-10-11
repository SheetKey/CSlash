{-# LANGUAGE RecordWildCards #-}

module CSlash.Unit.Info
  ( GenericUnitInfo(..)
  , GenUnitInfo
  , UnitInfo
  , UnitKeyInfo
  , mkUnitKeyInfo
  , mapUnitInfo
  , mkUnitPprInfo

  , mkUnit

  , PackageId(..)
  , PackageName(..)
  , Version(..)
  , unitPackageNameString
  , unitPackageIdString
  , pprUnitInfo

  , collectLibraryDirs
  , unitCsLibs
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
import CSlash.Unit.Ppr
import CSlash.Unit.Database

import CSlash.Settings

import Data.Version
import Data.Bifunctor
import Data.List (isPrefixOf, stripPrefix)

type GenUnitInfo unit
  = GenericUnitInfo PackageId PackageName unit ModuleName (GenModule (GenUnit unit))

type UnitKeyInfo = GenUnitInfo UnitKey

type UnitInfo = GenUnitInfo UnitId

mkUnitKeyInfo :: DbUnitInfo -> UnitKeyInfo
mkUnitKeyInfo = mapGenericUnitInfo
  mkUnitKey'
  mkPackageIdentifier'
  mkPackageName'
  mkModuleName'
  mkModule'
  where
    mkPackageIdentifier' = PackageId . mkFastStringByteString
    mkPackageName' = PackageName . mkFastStringByteString
    mkUnitKey' = UnitKey . mkFastStringByteString
    mkModuleName' = mkModuleNameFS . mkFastStringByteString
    mkVirtUnitKey' i = case i of
      DbInstUnitId cid insts -> mkVirtUnit (mkUnitKey' cid)
                                           (fmap (bimap mkModuleName' mkModule') insts)
      DbUnitId uid -> RealUnit (Definite (mkUnitKey' uid))
    mkModule' m = case m of
      DbModule uid n -> mkModule (mkVirtUnitKey' uid) (mkModuleName' n)
      DbModuleVar n -> mkHoleModule (mkModuleName' n)
 

mapUnitInfo :: IsUnitId v => (u -> v) -> GenUnitInfo u -> GenUnitInfo v
mapUnitInfo f = mapGenericUnitInfo f id id id (fmap (mapGenUnit f))

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

unitPackageIdString :: GenUnitInfo u -> String
unitPackageIdString pkg = unpackFS str
  where
    PackageId str = unitPackageId pkg

unitPackageNameString :: GenUnitInfo u -> String
unitPackageNameString pkg = unpackFS str
  where
    PackageName str = unitPackageName pkg

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

mkUnitPprInfo :: (u -> FastString) -> GenUnitInfo u -> UnitPprInfo
mkUnitPprInfo ufs i = UnitPprInfo
  (ufs (unitId i))
  (unitPackageNameString i)
  (unitPackageVersion i)

collectLibraryDirs :: Ways -> [UnitInfo] -> [FilePath]
collectLibraryDirs ws = ordNub . filter notNull . concatMap (libraryDirsForWay ws)

libraryDirsForWay :: Ways -> UnitInfo -> [String]
libraryDirsForWay ws
  | hasWay ws WayDyn = map ST.unpack . unitLibraryDynDirs
  | otherwise = map ST.unpack . unitLibraryDirs

unitCsLibs :: CsNameVersion -> Ways -> UnitInfo -> [String]
unitCsLibs namever ways0 p = map (mkDynName . addSuffix . ST.unpack) (unitLibraries p)
  where
    ways1 = removeWay WayDyn ways0

    tag = waysTag (fullWays ways1)
    rts_tag = waysTag ways1

    mkDynName x
      | not (ways0 `hasWay` WayDyn) = x
      | "CS" `isPrefixOf` x = x ++ dynLibSuffix namever
      | Just x' <- stripPrefix "C" x = x'
      | otherwise = panic ("Don't understand library name " ++ x)

    addSuffix rts@"CSrts" = rts ++ (expandTag rts_tag)
    addSuffix other = other ++ (expandTag tag)

    expandTag t | null t = ""
                | otherwise = '_' : t
