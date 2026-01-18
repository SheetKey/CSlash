{-# LANGUAGE DeriveGeneric #-}

module CSlash.CsToCore.Errors.Types where

import CSlash.Core (CoreExpr)
import CSlash.Core.DataCon
import CSlash.Core.ConLike
import CSlash.Core.Type
import CSlash.Driver.DynFlags (DynFlags)
import CSlash.Driver.Flags (WarningFlag)
import CSlash.Cs
-- import GHC.HsToCore.Pmc.Solver.Types
import CSlash.Types.Basic (Activation)
import CSlash.Types.Error
-- import GHC.Types.ForeignCall
import CSlash.Types.Id
import CSlash.Types.Name (Name)

import GHC.Generics (Generic)

data DsMessage
  = DsUnknownMessage (UnknownDiagnostic (DiagnosticOpts DsMessage))
  deriving Generic
