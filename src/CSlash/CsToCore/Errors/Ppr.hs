{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

module CSlash.CsToCore.Errors.Ppr where

-- import GHC.Core.Predicate (isEvVar)
import CSlash.Core.Type
import CSlash.Driver.Flags
import CSlash.Cs
import CSlash.CsToCore.Errors.Types
import CSlash.Types.Error
import CSlash.Types.Error.Codes
import CSlash.Types.Var (varType)
import CSlash.Types.SrcLoc
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
-- import GHC.HsToCore.Pmc.Ppr

instance Diagnostic DsMessage where
  type DiagnosticOpts DsMessage = NoDiagnosticOpts

  diagnosticMessage opts = \case
    DsUnknownMessage (UnknownDiagnostic f m)
      -> diagnosticMessage (f opts) m

  diagnosticReason = \case
    DsUnknownMessage m -> diagnosticReason m

  diagnosticHints = \case
    DsUnknownMessage m -> diagnosticHints m
