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
  , hoistTcRnMessage
  , hoistDsMessage
  ) where

import Data.Bifunctor
import Data.Typeable

import CSlash.Driver.DynFlags (DynFlags, PackageArg)
-- import CSlash.Driver.Flags (GeneralFlag (Opt_BuildingCabalPackage))
import CSlash.Types.Error
import CSlash.Unit.Module
import CSlash.Unit.State

import CSlash.Parser.Errors.Types ( PsMessage(PsHeaderMessage) )
import CSlash.CsToCore.Errors.Types ( DsMessage )
import CSlash.Cs.Extension          (Tc)

-- import Language.Haskell.Syntax.Decls (RuleDecl)
-- import qualified GHC.LanguageExtensions as LangExt

import GHC.Generics ( Generic )

import CSlash.Tc.Errors.Types
-- import GHC.Iface.Errors.Types

type WarningMessages = Messages CsMessage

type ErrorMessages = Messages CsMessage

data CsMessage where
  CsPsMessage :: PsMessage -> CsMessage
  CsTcRnMessage :: TcRnMessage -> CsMessage
  CsDsMessage :: DsMessage -> CsMessage
  CsDriverMessage :: DriverMessage -> CsMessage
  CsUnknownMessage :: (UnknownDiagnostic (DiagnosticOpts CsMessage)) -> CsMessage
  deriving Generic

data CsMessageOpts = CsMessageOpts
  { psMessageOpts :: DiagnosticOpts PsMessage
  , tcMessageOpts :: DiagnosticOpts TcRnMessage
  , dsMessageOpts :: DiagnosticOpts DsMessage
  , driverMessageOpts :: DiagnosticOpts DriverMessage
  }

hoistTcRnMessage :: Monad m => m (Messages TcRnMessage, a) -> m (Messages CsMessage, a)
hoistTcRnMessage = fmap (first (fmap CsTcRnMessage))

hoistDsMessage :: Monad m => m (Messages DsMessage, a) -> m (Messages CsMessage, a)
hoistDsMessage = fmap (first (fmap CsDsMessage))
  
type DriverMessages = Messages DriverMessage

data DriverMessage where
  DriverUnknownMessage :: UnknownDiagnostic (DiagnosticOpts DriverMessage) -> DriverMessage
  DriverPsHeaderMessage :: !PsMessage -> DriverMessage
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
