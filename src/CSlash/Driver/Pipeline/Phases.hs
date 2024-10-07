{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module CSlash.Driver.Pipeline.Phases (TPhase(..), PhaseHook(..)) where

import CSlash.Driver.Pipeline.Monad
import CSlash.Driver.Env.Types
import CSlash.Driver.DynFlags
import CSlash.Types.SourceFile
import CSlash.Unit.Module.ModSummary
import CSlash.Unit.Module.Status
import CSlash.Tc.Types ( FrontendResult )
import CSlash.Types.Error
import CSlash.Driver.Errors.Types
-- import GHC.Fingerprint.Type
import CSlash.Utils.Fingerprint
import CSlash.Unit.Module.Location ( ModLocation )
import CSlash.Unit.Module.ModIface
import CSlash.Driver.Phases

import CSlash.Language.Syntax.Module.Name ( ModuleName )
import CSlash.Unit.Home.ModInfo

data TPhase res where
  T_FileArgs
    :: CsEnv
    -> FilePath
    -> TPhase (DynFlags, Messages PsMessage, Messages DriverMessage)
  T_CsRecomp
    :: PipeEnv
    -> CsEnv
    -> FilePath
    -> CsSource
    -> TPhase (CsEnv, ModSummary, CsRecompStatus)
  T_Cs
    :: CsEnv
    -> ModSummary
    -> TPhase (FrontendResult, Messages CsMessage)
  T_CsPostTc
    :: CsEnv
    -> ModSummary
    -> FrontendResult
    -> Messages CsMessage
    -> Maybe Fingerprint
    -> TPhase CsBackendAction
  T_CsBackend
    :: PipeEnv
    -> CsEnv
    -> ModuleName
    -> CsSource
    -> ModLocation
    -> CsBackendAction
    -> TPhase ([FilePath], ModIface, HomeModLinkable, FilePath)
  T_LlvmOpt
    :: PipeEnv
    -> CsEnv
    -> FilePath
    -> TPhase FilePath
  T_LlvmLlc
    :: PipeEnv
    -> CsEnv
    -> FilePath
    -> TPhase FilePath
  T_LlvmAs
    :: PipeEnv
    -> CsEnv
    -> Maybe ModLocation
    -> FilePath
    -> TPhase FilePath
  T_MergeForeign
    :: PipeEnv
    -> CsEnv
    -> FilePath
    -> [FilePath]
    -> TPhase FilePath

data PhaseHook = PhaseHook (forall a. TPhase a -> IO a)
