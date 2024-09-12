module CSlash.Driver.Config.Diagnostic where

import CSlash.Driver.Flags
import CSlash.Driver.DynFlags

import CSlash.Utils.Outputable
import CSlash.Utils.Error (DiagOpts (..))
import CSlash.Driver.Errors.Types
  ( CsMessage, CsMessageOpts (..), PsMessage, DriverMessage, DriverMessageOpts (..) )
import CSlash.Driver.Errors.Ppr ()
-- import GHC.Tc.Errors.Types
-- import GHC.HsToCore.Errors.Types
import CSlash.Types.Error
-- import GHC.Iface.Errors.Types

initDiagOpts :: DynFlags -> DiagOpts
initDiagOpts dflags = DiagOpts
  { diag_warning_flags = warningFlags dflags
  , diag_fatal_warning_flags = fatalWarningFlags dflags
  , diag_custom_warning_categories = customWarningCategories dflags
  , diag_fatal_custom_warning_categories = fatalCustomWarningCategories dflags
  , diag_warn_is_error = gopt Opt_WarnIsError dflags
  , diag_reverse_errors = reverseErrors dflags
  , diag_max_errors = maxErrors dflags
  , diag_ppr_ctx = initSDocContext dflags defaultErrStyle
  }

initPrintConfig :: DynFlags -> DiagnosticOpts CsMessage
initPrintConfig dflags =
  CsMessageOpts { psMessageOpts = initPsMessageOpts dflags
                , driverMessageOpts = initDriverMessageOpts dflags
                }

initPsMessageOpts :: DynFlags -> DiagnosticOpts PsMessage
initPsMessageOpts _ = NoDiagnosticOpts

initDriverMessageOpts :: DynFlags -> DiagnosticOpts DriverMessage
initDriverMessageOpts dflags = DriverMessageOpts (initPsMessageOpts dflags)
