{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}

module CSlash.Driver.Errors.Types
  ( CsMessage(..)
  , CsMessageOpts(..)
  , DriverMessage(..)
  , DriverMessageOpts(..)
  , DriverMessages, PsMessage(PsHeaderMessage)
  , WarningMessages
  , ErrorMessages
  ) where

import Data.Bifunctor
import Data.Typeable

import CSlash.Driver.DynFlags (DynFlags, PackageArg)
-- import CSlash.Driver.Flags (GeneralFlag (Opt_BuildingCabalPackage))
import CSlash.Types.Error
import CSlash.Unit.Module
import CSlash.Unit.State

import CSlash.Parser.Errors.Types ( PsMessage(PsHeaderMessage) )
-- import GHC.HsToCore.Errors.Types ( DsMessage )
import CSlash.Cs.Extension          (Tc)

-- import Language.Haskell.Syntax.Decls (RuleDecl)
-- import qualified GHC.LanguageExtensions as LangExt

import GHC.Generics ( Generic )

-- import GHC.Tc.Errors.Types
-- import GHC.Iface.Errors.Types

type WarningMessages = Messages CsMessage

type ErrorMessages = Messages CsMessage

data CsMessage where
  CsPsMessage :: PsMessage -> CsMessage
  CsDriverMessage :: DriverMessage -> CsMessage
  CsUnknownMessage :: (UnknownDiagnostic (DiagnosticOpts CsMessage)) -> CsMessage
  deriving Generic

data CsMessageOpts = CsMessageOpts
  { psMessageOpts :: DiagnosticOpts PsMessage
  , driverMessageOpts :: DiagnosticOpts DriverMessage
  }
  
type DriverMessages = Messages DriverMessage

data DriverMessage where
  DriverUnknownMessage :: UnknownDiagnostic (DiagnosticOpts DriverMessage) -> DriverMessage
  DriverMissingHomeModules :: UnitId -> [ModuleName] -> DriverMessage
  DriverUnknownReexportedModules :: UnitId -> [ModuleName] -> DriverMessage
  DriverUnknownHiddenModules :: UnitId -> [ModuleName] -> DriverMessage
  DriverUnusedPackages :: [(UnitId, PackageName, Version, PackageArg)] -> DriverMessage
  DriverDuplicatedModuleDeclaration :: !Module -> [FilePath] -> DriverMessage
  DriverModuleNotFound :: !ModuleName -> DriverMessage
  DriverFileModuleNameMismatch :: !ModuleName -> !ModuleName -> DriverMessage
  DriverFileNotFound :: !FilePath -> DriverMessage
  DriverRedirectedNoMain :: !ModuleName -> DriverMessage
  DriverHomePackagesNotClosed :: ![UnitId] -> DriverMessage
  DriverInconsistentDynFlags :: String -> DriverMessage
  DriverUnrecognizedFlag :: String -> DriverMessage
  DriverDeprecatedFlag :: String -> String -> DriverMessage

deriving instance Generic DriverMessage

data DriverMessageOpts = DriverMessageOpts
  { psDiagnosticOpts :: DiagnosticOpts PsMessage
  }
