{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}

module CSlash.Driver.Errors.Ppr () where

import Prelude hiding ((<>))

import CSlash.Driver.Errors.Types
import CSlash.Driver.Flags
import CSlash.Driver.DynFlags
import CSlash.CsToCore.Errors.Ppr ()
import CSlash.Parser.Errors.Ppr ()
import CSlash.Types.Error
import CSlash.Types.Error.Codes
import CSlash.Unit.Types
import CSlash.Utils.Outputable
import CSlash.Unit.Module
import CSlash.Unit.State
import CSlash.Types.Hint
import CSlash.Types.SrcLoc
import Data.Version

-- import Language.Haskell.Syntax.Decls (RuleDecl(..))
import CSlash.Tc.Errors.Types (TcRnMessage)
import CSlash.CsToCore.Errors.Types (DsMessage)
-- import GHC.Iface.Errors.Types
import CSlash.Tc.Errors.Ppr ()
-- import GHC.Iface.Errors.Ppr ()

import CSlash.Utils.Panic

instance HasDefaultDiagnosticOpts CsMessageOpts where
  defaultOpts = CsMessageOpts (defaultDiagnosticOpts @PsMessage)
                              (defaultDiagnosticOpts @TcRnMessage)
                              (defaultDiagnosticOpts @DsMessage)
                              (defaultDiagnosticOpts @DriverMessage)

instance Diagnostic CsMessage where
  type DiagnosticOpts CsMessage = CsMessageOpts
  diagnosticMessage opts = \case
    CsPsMessage m -> diagnosticMessage (psMessageOpts opts) m
    CsTcRnMessage m -> diagnosticMessage (tcMessageOpts opts) m
    CsDsMessage m -> diagnosticMessage (dsMessageOpts opts) m
    CsDriverMessage m -> diagnosticMessage (driverMessageOpts opts) m
    CsUnknownMessage (UnknownDiagnostic f m) -> diagnosticMessage (f opts) m

  diagnosticReason = \case
    CsPsMessage m -> diagnosticReason m
    CsTcRnMessage m -> diagnosticReason m
    CsDsMessage m -> diagnosticReason m
    CsDriverMessage m -> diagnosticReason m
    CsUnknownMessage m -> diagnosticReason m

  diagnosticHints = \case
    CsPsMessage m -> diagnosticHints m
    CsTcRnMessage m -> diagnosticHints m
    CsDsMessage m -> diagnosticHints m
    CsDriverMessage m -> diagnosticHints m
    CsUnknownMessage m -> diagnosticHints m

  diagnosticCode = constructorCode

instance HasDefaultDiagnosticOpts DriverMessageOpts where
  defaultOpts = DriverMessageOpts (defaultDiagnosticOpts @PsMessage)

instance Diagnostic DriverMessage where
  type DiagnosticOpts DriverMessage = DriverMessageOpts
  diagnosticMessage opts = \case
    DriverUnknownMessage (UnknownDiagnostic f m)
      -> diagnosticMessage (f opts) m
    DriverMissingHomeModules uid missing
      -> let msg = hang
                   (text "Modules are not listed in options for"
                    <+> quotes (ppr uid) <+> text "but needed for compilation:")
                   4 (sep (map ppr missing))
         in mkSimpleDecorated msg
    DriverUnknownReexportedModules uid missing
      -> let msg = hang
                   (text "Modules are listed as reexported in options for"
                    <+> quotes (ppr uid)
                    <+> text "but can't be found in any dependency:")
                   4 (sep (map ppr missing))
         in mkSimpleDecorated msg
    DriverUnknownHiddenModules uid missing
      -> let msg = hang
                   (text "Modules are listed as hidden in options for"
                    <+> quotes (ppr uid)
                    <+> text "but not part of the unit:")
                   4 (sep (map ppr missing))
         in mkSimpleDecorated msg
    DriverUnusedPackages unusedArgs
      -> let msg = vcat [ text "The following packages were specified" <+>
                          text "via -package or -package-id flags,"
                        , text "but were not needed for compilation:"
                        , nest 2 (vcat (map (withDash . displayOneUnused) unusedArgs))
                        ]
         in mkSimpleDecorated msg
      where
        withDash :: SDoc -> SDoc
        withDash = (<+>) (text "-")
        displayOneUnused (_uid, pn, v, f) =
          ppr pn <> text "-" <> text (showVersion v)
          <+> parens (suffix f)
        suffix f = text "exposed by flag" <+> pprUnusedArg f
        pprUnusedArg :: PackageArg -> SDoc
        pprUnusedArg (PackageArg str) = text "-package" <+> text str
        pprUnusedArg (UnitIdArg uid) = text "-package-id" <+> ppr uid
    DriverDuplicatedModuleDeclaration mod files
      -> let msg = text "module" <+> quotes (ppr mod)
                   <+> text "is defined in multiple files:"
                   <+> sep (map text files)
         in mkSimpleDecorated msg
    DriverModuleNotFound mod
      -> mkSimpleDecorated $ text "module" <+> quotes (ppr mod) <+> text "cannot be found locally"
    DriverFileModuleNameMismatch actual expected
      -> let msg = text "File name does not match module name:"
                   $$ text "Saw     :" <+> quotes (ppr actual)
                   $$ text "Expected:" <+> quotes (ppr expected)
         in mkSimpleDecorated msg
    DriverFileNotFound filePath
      -> mkSimpleDecorated $ text "Can't find" <+> text filePath
    DriverRedirectedNoMain mod_name
      -> let msg = text ("Output was redirected with -0, "
                         ++ "but no output will be generated.")
                   $$ (text "There is no module named"
                       <+> quotes (ppr mod_name) <> text ".")
         in mkSimpleDecorated msg
    DriverHomePackagesNotClosed needed_unit_ids
      -> let msg = vcat ([ text "Home units are not closed."
                         , text "It is necessary to also load the following units:" ]
                         ++ map (\uid -> text "-" <+> ppr uid) needed_unit_ids)
         in mkSimpleDecorated msg
    DriverInconsistentDynFlags msg
      -> mkSimpleDecorated $ text msg
    DriverUnrecognizedFlag arg
      -> mkSimpleDecorated $ text $ "unrecognized warning flag: -" ++ arg
    DriverDeprecatedFlag arg msg
      -> mkSimpleDecorated $ text $ arg ++ " is deprecated: " ++ msg
    _ -> mkSimpleDecorated $ text "diagnosticMessage DriverMessage"

  diagnosticReason = \case
    DriverUnknownMessage m
      -> diagnosticReason m
    DriverMissingHomeModules{}
      -> WarningWithFlag Opt_WarnMissingHomeModules
    DriverUnknownHiddenModules {}
      -> ErrorWithoutFlag
    DriverUnknownReexportedModules {}
      -> ErrorWithoutFlag
    DriverUnusedPackages{}
      -> WarningWithFlag Opt_WarnUnusedPackages
    DriverDuplicatedModuleDeclaration{}
      -> ErrorWithoutFlag
    DriverModuleNotFound{}
      -> ErrorWithoutFlag
    DriverFileModuleNameMismatch{}
      -> ErrorWithoutFlag
    DriverFileNotFound{}
      -> ErrorWithoutFlag
    DriverRedirectedNoMain {}
      -> ErrorWithoutFlag
    DriverHomePackagesNotClosed {}
      -> ErrorWithoutFlag
    DriverInconsistentDynFlags {}
      -> WarningWithFlag Opt_WarnInconsistentFlags
    DriverUnrecognizedFlag {}
      -> WarningWithFlag Opt_WarnUnrecognizedWarningFlags
    DriverDeprecatedFlag {}
      -> WarningWithFlag Opt_WarnDeprecatedFlags
    _ -> panic "diagnosticReason DriverMessage"

  diagnosticHints = \case
    DriverUnknownMessage m
      -> diagnosticHints m
    DriverMissingHomeModules{}
      -> noHints
    DriverUnknownHiddenModules {}
      -> noHints
    DriverUnknownReexportedModules {}
      -> noHints
    DriverUnusedPackages{}
      -> noHints
    DriverDuplicatedModuleDeclaration{}
      -> noHints
    DriverModuleNotFound{}
      -> noHints
    DriverFileModuleNameMismatch{}
      -> noHints
    DriverFileNotFound{}
      -> noHints
    DriverRedirectedNoMain {}
      -> noHints
    DriverHomePackagesNotClosed {}
      -> noHints
    DriverInconsistentDynFlags {}
      -> noHints
    DriverUnrecognizedFlag {}
      -> noHints
    DriverDeprecatedFlag {}
      -> noHints
    _ -> panic "diagnosticHints DriverMessage"

  diagnosticCode = constructorCode
