{-# LANGUAGE DeriveGeneric #-}

module CSlash.Iface.Errors.Types where

import CSlash.Types.Name (Name)
import CSlash.Types.TyThing (TyThing)
import CSlash.Unit.Types (Module, InstalledModule, UnitId, Unit)
import CSlash.Unit.State (UnitState, ModuleSuggestion, ModuleOrigin, UnusableUnit, UnitInfo)
import CSlash.Language.Syntax.Module.Name ( ModuleName )
import CSlash.Unit.Module.Location

import GHC.Generics ( Generic )
import GHC.Exception.Type (SomeException)

data IfaceMessageOpts = IfaceMessageOpts
  { ifaceShowTriedFiles :: !Bool
  }

data MissingInterfaceError
  = HomeModError !InstalledModule !ModLocation
  | DynamicHashMismatchError !Module !ModLocation
  | CantFindErr !UnitState FindingModuleOrInterface CantFindInstalled
  | BadIfaceFile ReadInterfaceError
  | FailedToLoadDynamicInterface Module ReadInterfaceError
  deriving Generic

data ReadInterfaceError
  = ExceptionOccurred FilePath SomeException
  | HiModuleNameMismatchWarn FilePath Module Module
  deriving Generic

data CantFindInstalledReason
  = NoUnitIdMatching UnitId [UnitInfo]
  | MissingPackageFiles UnitId [FilePath]
  | MissingPackageWayFiles String UnitId [FilePath]
  | ModuleSuggestion [ModuleSuggestion] [FilePath]
  | NotAModule
  | CouldntFindInFiles [FilePath]
  | GenericMissing [(Unit, Maybe UnitInfo)] [Unit] [UnusableUnit] [FilePath]
  | MultiplePackages [(Module, ModuleOrigin)]
  deriving Generic

data CantFindInstalled = CantFindInstalled ModuleName CantFindInstalledReason
  deriving Generic

data FindingModuleOrInterface
  = FindingModule
  | FindingInterface
