module CSlash.Driver.Flags
  ( DumpFlag(..)
  , getDumpFlagFrom
  , GeneralFlag(..)
  , optimisationFlags

  , WarningGroup(..)
  , warningGroupName
  , warningGroupFlags
  , warningGroupIncludesExtendedWarnings
  , WarningFlag(..)
  , warnFlagNames
  , warningGroups
  , warningHierarchies
  , smallestWarningGroups
  , smallestWarningGroupsForCategory

  , standardWarnings
  , minusWOpts
  , minusWallOpts
  , minusWeverythingOpts
  , unusedBindsFlags
  ) where

import CSlash.Utils.Outputable
import CSlash.Data.EnumSet as EnumSet

import Control.Monad (guard)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (fromMaybe,mapMaybe)

data DumpFlag
  = Opt_D_dump_llvm
  | Opt_D_dump_core_stats
  | Opt_D_dump_ds
  | Opt_D_dump_ds_preopt
  | Opt_D_dump_inlinings              
  | Opt_D_dump_verbose_inlinings      
  | Opt_D_dump_simpl_trace            
  | Opt_D_dump_occur_anal
  | Opt_D_dump_parsed
  | Opt_D_dump_parsed_ast
  | Opt_D_dump_rn
  | Opt_D_dump_rn_ast
  | Opt_D_dump_simpl
  | Opt_D_dump_simpl_iterations
  | Opt_D_dump_spec
  | Opt_D_dump_spec_constr
  | Opt_D_dump_prep
  | Opt_D_dump_late_cc
  | Opt_D_dump_call_arity
  | Opt_D_dump_exitify
  | Opt_D_dump_dmdanal
  | Opt_D_dump_dmd_signatures
  | Opt_D_dump_cpranal
  | Opt_D_dump_cpr_signatures
  | Opt_D_dump_tc
  | Opt_D_dump_tc_ast
  | Opt_D_dump_hie
  | Opt_D_dump_types                  
  | Opt_D_dump_cse
  | Opt_D_dump_float_out
  | Opt_D_dump_float_in
  | Opt_D_dump_liberate_case
  | Opt_D_dump_static_argument_transformation
  | Opt_D_dump_rn_trace               
  | Opt_D_dump_rn_stats               
  | Opt_D_dump_simpl_stats
  | Opt_D_dump_cs_trace               
  | Opt_D_dump_tc_trace               
  | Opt_D_dump_ec_trace
  | Opt_D_dump_if_trace
  | Opt_D_dump_BCOs
  | Opt_D_dump_ticked
  | Opt_D_dump_rtti
  | Opt_D_source_stats
  | Opt_D_dump_hi
  | Opt_D_dump_hi_diffs
  | Opt_D_dump_mod_cycles             
  | Opt_D_dump_mod_map
  | Opt_D_dump_timings
  | Opt_D_verbose_core2core           
  | Opt_D_dump_debug
  | Opt_D_ppr_debug
  | Opt_D_no_debug_output
  | Opt_D_dump_faststrings
  | Opt_D_faststring_stats
  | Opt_D_ipe_stats
  deriving (Eq, Ord, Show, Enum, Bounded)

getDumpFlagFrom
  :: (a -> Int)
  -> (a -> EnumSet DumpFlag)
  -> DumpFlag -> a -> Bool
getDumpFlagFrom getVerbosity getFlags f x
  = (f `EnumSet.member` getFlags x)
  || (getVerbosity x >= 4 && enabledIfVerbose f)

enabledIfVerbose :: DumpFlag -> Bool
enabledIfVerbose Opt_D_dump_tc_trace               = False
enabledIfVerbose Opt_D_dump_rn_trace               = False
enabledIfVerbose Opt_D_dump_cs_trace               = False
enabledIfVerbose Opt_D_dump_if_trace               = False
enabledIfVerbose Opt_D_dump_tc                     = False
enabledIfVerbose Opt_D_dump_rn                     = False
enabledIfVerbose Opt_D_dump_rn_stats               = False
enabledIfVerbose Opt_D_dump_hi_diffs               = False
enabledIfVerbose Opt_D_verbose_core2core           = False
enabledIfVerbose Opt_D_dump_simpl_trace            = False
enabledIfVerbose Opt_D_dump_rtti                   = False
enabledIfVerbose Opt_D_dump_inlinings              = False
enabledIfVerbose Opt_D_dump_verbose_inlinings      = False
enabledIfVerbose Opt_D_dump_core_stats             = False
enabledIfVerbose Opt_D_dump_types                  = False
enabledIfVerbose Opt_D_dump_simpl_iterations       = False
enabledIfVerbose Opt_D_dump_ticked                 = False
enabledIfVerbose Opt_D_dump_mod_cycles             = False
enabledIfVerbose Opt_D_dump_mod_map                = False
enabledIfVerbose Opt_D_dump_ec_trace               = False
enabledIfVerbose _                                 = True


data GeneralFlag
  = Opt_DumpToFile                     -- ^ Append dump output to files instead of stdout.
  | Opt_DumpWithWays                   -- ^ Use foo.ways.<dumpFlag> instead of foo.<dumpFlag>
  | Opt_D_dump_minimal_imports
  | Opt_DoCoreLinting
  | Opt_DoBoundsChecking

  | Opt_WarnIsError                    -- -Werror; makes warnings fatal
  | Opt_ShowWarnGroups                 -- Show the group a warning belongs to
  | Opt_HideSourcePaths                -- Hide module source/object paths

  | Opt_PrintUnicodeSyntax
  | Opt_PrintExpandedSynonyms
  | Opt_PrintTypecheckerElaboration

  -- optimisation opts
  | Opt_CallArity
  | Opt_Exitification
  | Opt_LateDmdAnal
  | Opt_KillAbsence
  | Opt_KillOneShot
  | Opt_FloatIn
  | Opt_LocalFloatOut
  | Opt_LocalFloatOutTopLevel 
  | Opt_LateSpecialise
  | Opt_Specialise
  | Opt_SpecialiseAggressively
  | Opt_CrossModuleSpecialise
  | Opt_PolymorphicSpecialisation
  | Opt_InlineGenerics
  | Opt_InlineGenericsAggressively
  | Opt_StaticArgumentTransformation
  | Opt_CSE
  | Opt_LiberateCase
  | Opt_SpecConstr
  | Opt_SpecConstrKeen
  | Opt_SpecialiseIncoherents
  | Opt_DoLambdaEtaExpansion
  | Opt_DoCleverArgEtaExpansion
  | Opt_IgnoreAsserts
  | Opt_DoEtaReduction
  | Opt_CaseMerge
  | Opt_CaseFolding                    -- Constant folding through case-expressions
  | Opt_DictsCheap
  | Opt_LlvmFillUndefWithGarbage       -- Testing for undef bugs (hidden flag)
  | Opt_IrrefutableTuples
  | Opt_OmitYields
  | Opt_Loopification                  -- See Note [Self-recursive tail calls]
  | Opt_CfgBlocklayout             -- ^ Use the cfg based block layout algorithm.
  | Opt_WeightlessBlocklayout         -- ^ Layout based on last instruction per block.
  | Opt_CprAnal
  | Opt_SolveConstantDicts
  | Opt_AlignmentSanitisation
  | Opt_CatchNonexhaustiveCases
  | Opt_NumConstantFolding
  | Opt_CoreConstantFolding
  | Opt_FastPAPCalls

  -- Inference flags
  | Opt_DoTagInferenceChecks

  -- PreInlining is on by default. The option is there just to see how
  -- bad things get if you turn it off!
  | Opt_SimplPreInlining

  -- Interface files
  | Opt_IgnoreInterfacePragmas
  | Opt_OmitInterfacePragmas
  | Opt_ExposeAllUnfoldings
  | Opt_WriteInterface -- forces .hi files to be written even with -fno-code
  | Opt_WriteHie -- generate .hie files

  -- profiling opts
  | Opt_AutoSccsOnIndividualCafs
  | Opt_ProfCountEntries
  | Opt_ProfLateInlineCcs
  | Opt_ProfLateCcs
  | Opt_ProfLateOverloadedCcs
  | Opt_ProfLateoverloadedCallsCCs
  | Opt_ProfManualCcs -- ^ Ignore manual SCC annotations

  -- misc opts
  | Opt_ForceRecomp
  | Opt_IgnoreOptimChanges
  | Opt_IgnorePcChanges
  | Opt_ExcessPrecision
  | Opt_EagerBlackHoling
  | Opt_NoCsMain
  | Opt_SplitSections
  | Opt_HideAllPackages
  | Opt_HideAllPluginPackages
  | Opt_PrintBindResult
  | Opt_BreakOnException
  | Opt_BreakOnError
  | Opt_PrintEvldWithShow
  | Opt_PrintBindContents
  | Opt_GenManifest
  | Opt_EmbedManifest
  | Opt_SharedImplib
  | Opt_InsertBreakpoints
  | Opt_ValidateHie
  | Opt_NoIt
  | Opt_HelpfulErrors
  | Opt_DeferTypeErrors
  | Opt_DeferTypedHoles
  | Opt_DeferOutOfScopeVariables
  | Opt_PIC                         -- ^ @-fPIC@
  | Opt_PIE                         -- ^ @-fPIE@
  | Opt_PICExecutable               -- ^ @-pie@
  | Opt_ExternalDynamicRefs
  -- | Opt_Ticky
  -- | Opt_Ticky_Allocd
  -- | Opt_Ticky_LNE
  -- | Opt_Ticky_Dyn_Thunk
  -- | Opt_Ticky_Tag
  -- | Opt_Ticky_AP                    -- ^ Use regular thunks even when we could use std ap thunks in order to get entry counts
  | Opt_RPath
  | Opt_RelativeDynlibPaths
  | Opt_Pc
  | Opt_FamAppCache
  | Opt_VersionMacros
  | Opt_WholeArchiveCsLibs
   -- copy all libs into a single folder prior to linking binaries
   -- this should alleviate the excessive command line limit restrictions
   -- on windows, by only requiring a single -L argument instead of
   -- one for each dependency.  At the time of this writing, gcc
   -- forwards all -L flags to the collect2 command without using a
   -- response file and as such breaking apart.
  | Opt_SingleLibFolder
  | Opt_ExposeInternalSymbols
  | Opt_KeepCAFs
  | Opt_KeepGoing
  | Opt_LinkRts

  -- output style opts
  | Opt_ErrorSpans -- Include full span info in error messages,
                   -- instead of just the start position.
  | Opt_DeferDiagnostics
  | Opt_DiagnosticsAsJSON  -- ^ Dump diagnostics as JSON
  | Opt_DiagnosticsShowCaret -- Show snippets of offending code
  | Opt_PprCaseAsLet
  -- | Opt_ShowHoleConstraints
  --  -- Options relating to the display of valid hole fits
  --  -- when generating an error message for a typed hole
  --  -- See Note [Valid hole fits include ...] in GHC.Tc.Errors.Hole
  -- | Opt_ShowValidHoleFits
  -- | Opt_SortValidHoleFits
  -- | Opt_SortBySizeHoleFits
  -- | Opt_SortBySubsumHoleFits
  -- | Opt_AbstractRefHoleFits
  -- | Opt_UnclutterValidHoleFits
  -- | Opt_ShowTypeAppOfHoleFits
  -- | Opt_ShowTypeAppVarsOfHoleFits
  -- | Opt_ShowDocsOfHoleFits
  -- | Opt_ShowTypeOfHoleFits
  -- | Opt_ShowProvOfHoleFits
  -- | Opt_ShowMatchesOfHoleFits

  | Opt_ShowLoadedModules
  | Opt_HexWordLiterals

  -- Suppress module id prefixes on variables.
  | Opt_SuppressModulePrefixes
  -- Suppress info such as arity and unfoldings on identifiers.
  | Opt_SuppressIdInfo
  -- Suppress separate type signatures in core, but leave types on
  -- lambda bound vars
  | Opt_SuppressUnfoldings
  -- Suppress the details of even stable unfoldings
  | Opt_SuppressTypeSignatures
  -- Suppress unique ids on variables.
  -- Except for uniques, as some simplifier phases introduce new
  -- variables that have otherwise identical names.
  | Opt_SuppressUniques
  | Opt_SuppressTicks
  | Opt_SuppressTimestamps -- ^ Suppress timestamps in dumps
  | Opt_SuppressCoreSizes  -- ^ Suppress per binding Core size stats in dumps

  -- Error message suppression
  | Opt_ShowErrorContext

  -- temporary flags
  | Opt_AutoLinkPackages
  | Opt_ImplicitImportQualified

  -- keeping stuff
  | Opt_KeepHiDiffs
  | Opt_KeepSFiles
  | Opt_KeepTmpFiles
  | Opt_KeepRawTokenStream
  | Opt_KeepLlvmFiles
  | Opt_KeepHiFiles
  | Opt_KeepOFiles

  | Opt_BuildDynamicToo
  | Opt_WriteIfSimplifiedCore

  | Opt_G_NoStateHack
  deriving (Eq, Show, Enum)

optimisationFlags :: EnumSet GeneralFlag
optimisationFlags = EnumSet.fromList
  [ Opt_CallArity
  , Opt_LateDmdAnal
  , Opt_KillAbsence
  , Opt_KillOneShot
  , Opt_FloatIn
  , Opt_LateSpecialise
  , Opt_Specialise
  , Opt_SpecialiseAggressively
  , Opt_CrossModuleSpecialise
  , Opt_StaticArgumentTransformation
  , Opt_CSE
  , Opt_LiberateCase
  , Opt_SpecConstr
  , Opt_SpecConstrKeen
  , Opt_DoLambdaEtaExpansion
  , Opt_IgnoreAsserts
  , Opt_DoEtaReduction
  , Opt_CaseMerge
  , Opt_CaseFolding
  , Opt_DictsCheap
  , Opt_IrrefutableTuples
  , Opt_Loopification
  , Opt_WeightlessBlocklayout
  , Opt_CprAnal
  , Opt_SolveConstantDicts
  ]

data WarningFlag =
     Opt_WarnDuplicateExports
   | Opt_WarnRedundantConstraints
   | Opt_WarnImplicitPrelude
   | Opt_WarnIncompletePatterns
   | Opt_WarnIncompleteUniPatterns
   | Opt_WarnOverflowedLiterals
   | Opt_WarnEmptyEnumerations
   | Opt_WarnMissingFields
   | Opt_WarnMissingImportList
   | Opt_WarnMissingMethods
   | Opt_WarnMissingSignatures
   | Opt_WarnMissingLocalSignatures
   | Opt_WarnNameShadowing
   | Opt_WarnOverlappingPatterns
   | Opt_WarnTypeDefaults
   | Opt_WarnMonomorphism
   | Opt_WarnUnusedTopBinds
   | Opt_WarnUnusedLocalBinds
   | Opt_WarnUnusedPatternBinds
   | Opt_WarnUnusedImports
   | Opt_WarnUnusedMatches
   | Opt_WarnUnusedTypePatterns
   | Opt_WarnUnrecognizedWarningFlags
   | Opt_WarnUnusedForalls
   | Opt_WarnDeprecatedFlags
   | Opt_WarnDodgyImports
   | Opt_WarnOrphans
   | Opt_WarnIdentities
   | Opt_WarnTabs
   | Opt_WarnDodgyForeignImports
   | Opt_WarnUnsupportedLlvmVersion
   | Opt_WarnInlineRuleShadowing
   | Opt_WarnTypedHoles
   | Opt_WarnPartialTypeSignatures
   | Opt_WarnMissingExportedSignatures
   | Opt_WarnDeferredTypeErrors
   | Opt_WarnDeferredOutOfScopeVariables
   | Opt_WarnMissingHomeModules
   | Opt_WarnPartialFields                       
   | Opt_WarnMissingExportList
   | Opt_WarnInaccessibleCode
   | Opt_WarnPrepositiveQualifiedModule          
   | Opt_WarnUnusedPackages                      
   | Opt_WarnCompatUnqualifiedImports            
   | Opt_WarnOperatorWhitespace                  
   | Opt_WarnMissingKindSignatures               
   | Opt_WarnMissingPolyKindSignatures           
   | Opt_WarnUnicodeBidirectionalFormatCharacters
   | Opt_WarnTermVariableCapture
   | Opt_WarnInconsistentFlags
   deriving (Eq, Ord, Show, Enum, Bounded)

warnFlagNames :: WarningFlag -> NonEmpty String
warnFlagNames wflag = case wflag of
  Opt_WarnTermVariableCapture                     -> "term-variable-capture" :| []
  Opt_WarnDeferredTypeErrors                      -> "deferred-type-errors" :| []
  Opt_WarnDeferredOutOfScopeVariables             -> "deferred-out-of-scope-variables" :| []
  Opt_WarnDeprecatedFlags                         -> "deprecated-flags" :| []
  Opt_WarnDodgyForeignImports                     -> "dodgy-foreign-imports" :| []
  Opt_WarnEmptyEnumerations                       -> "empty-enumerations" :| []
  Opt_WarnRedundantConstraints                    -> "redundant-constraints" :| []
  Opt_WarnDuplicateExports                        -> "duplicate-exports" :| []
  Opt_WarnInaccessibleCode                        -> "inaccessible-code" :| []
  Opt_WarnImplicitPrelude                         -> "implicit-prelude" :| []
  Opt_WarnIncompletePatterns                      -> "incomplete-patterns" :| []
  Opt_WarnIncompleteUniPatterns                   -> "incomplete-uni-patterns" :| []
  Opt_WarnInlineRuleShadowing                     -> "inline-rule-shadowing" :| []
  Opt_WarnIdentities                              -> "identities" :| []
  Opt_WarnMissingFields                           -> "missing-fields" :| []
  Opt_WarnMissingImportList                       -> "missing-import-lists" :| []
  Opt_WarnMissingExportList                       -> "missing-export-lists" :| []
  Opt_WarnMissingLocalSignatures                  -> "missing-local-signatures" :| []
  Opt_WarnMissingMethods                          -> "missing-methods" :| []
  Opt_WarnMissingSignatures                       -> "missing-signatures" :| []
  Opt_WarnMissingKindSignatures                   -> "missing-kind-signatures" :| []
  Opt_WarnMissingPolyKindSignatures               -> "missing-poly-kind-signatures" :| []
  Opt_WarnMissingExportedSignatures               -> "missing-exported-signatures" :| []
  Opt_WarnMonomorphism                            -> "monomorphism-restriction" :| []
  Opt_WarnNameShadowing                           -> "name-shadowing" :| []
  Opt_WarnDodgyImports                            -> "dodgy-imports" :| []
  Opt_WarnOrphans                                 -> "orphans" :| []
  Opt_WarnOverflowedLiterals                      -> "overflowed-literals" :| []
  Opt_WarnOverlappingPatterns                     -> "overlapping-patterns" :| []
  Opt_WarnTabs                                    -> "tabs" :| []
  Opt_WarnTypeDefaults                            -> "type-defaults" :| []
  Opt_WarnTypedHoles                              -> "typed-holes" :| []
  Opt_WarnPartialTypeSignatures                   -> "partial-type-signatures" :| []
  Opt_WarnUnsupportedLlvmVersion                  -> "unsupported-llvm-version" :| []
  Opt_WarnUnusedForalls                           -> "unused-foralls" :| []
  Opt_WarnUnusedImports                           -> "unused-imports" :| []
  Opt_WarnUnusedLocalBinds                        -> "unused-local-binds" :| []
  Opt_WarnUnusedMatches                           -> "unused-matches" :| []
  Opt_WarnUnusedPatternBinds                      -> "unused-pattern-binds" :| []
  Opt_WarnUnusedTopBinds                          -> "unused-top-binds" :| []
  Opt_WarnUnusedTypePatterns                      -> "unused-type-patterns" :| []
  Opt_WarnMissingHomeModules                      -> "missing-home-modules" :| []
  Opt_WarnUnrecognizedWarningFlags                -> "unrecognized-warning-flags" :| []
  Opt_WarnPartialFields                           -> "partial-fields" :| []
  Opt_WarnPrepositiveQualifiedModule              -> "prepositive-qualified-module" :| []
  Opt_WarnUnusedPackages                          -> "unused-packages" :| []
  Opt_WarnCompatUnqualifiedImports                -> "compat-unqualified-imports" :| []
  Opt_WarnOperatorWhitespace                      -> "operator-whitespace" :| []
  Opt_WarnUnicodeBidirectionalFormatCharacters    -> "unicode-bidirectional-format-characters" :| []
  Opt_WarnInconsistentFlags                       -> "inconsistent-flags" :| []

data WarningGroup = W_unused_binds
                  | W_extended_warnings
                  | W_default
                  | W_extra
                  | W_all
                  | W_everything
  deriving (Bounded, Enum, Eq)

warningGroupName :: WarningGroup -> String
warningGroupName W_unused_binds      = "unused-binds"
warningGroupName W_extended_warnings = "extended-warnings"
warningGroupName W_default           = "default"
warningGroupName W_extra             = "extra"
warningGroupName W_all               = "all"
warningGroupName W_everything        = "everything"

warningGroupFlags :: WarningGroup -> [WarningFlag]
warningGroupFlags W_unused_binds      = unusedBindsFlags
warningGroupFlags W_extended_warnings = []
warningGroupFlags W_default           = standardWarnings
warningGroupFlags W_extra             = minusWOpts
warningGroupFlags W_all               = minusWallOpts
warningGroupFlags W_everything        = minusWeverythingOpts

warningGroupIncludesExtendedWarnings :: WarningGroup -> Bool
warningGroupIncludesExtendedWarnings W_unused_binds      = False
warningGroupIncludesExtendedWarnings W_extended_warnings = True
warningGroupIncludesExtendedWarnings W_default           = True
warningGroupIncludesExtendedWarnings W_extra             = True
warningGroupIncludesExtendedWarnings W_all               = True
warningGroupIncludesExtendedWarnings W_everything        = True

warningGroups :: [WarningGroup]
warningGroups = [minBound..maxBound]

warningHierarchies :: [[WarningGroup]]
warningHierarchies = hierarchies ++ map (:[]) rest
  where
    hierarchies = [[W_default, W_extra, W_all]]
    rest = filter (`notElem` W_everything : concat hierarchies) warningGroups

smallestWarningGroups :: WarningFlag -> [WarningGroup]
smallestWarningGroups flag = mapMaybe go warningHierarchies where
    go (group:rest) = fromMaybe (go rest) $ do
        guard (flag `elem` warningGroupFlags group)
        pure (Just group)
    go [] = Nothing

smallestWarningGroupsForCategory :: [WarningGroup]
smallestWarningGroupsForCategory = [W_extended_warnings]

standardWarnings :: [WarningFlag]
standardWarnings
    = [ Opt_WarnOverlappingPatterns,
        Opt_WarnDeprecatedFlags,
        Opt_WarnDeferredTypeErrors,
        Opt_WarnTypedHoles,
        Opt_WarnDeferredOutOfScopeVariables,
        Opt_WarnPartialTypeSignatures,
        Opt_WarnDuplicateExports,
        Opt_WarnOverflowedLiterals,
        Opt_WarnEmptyEnumerations,
        Opt_WarnMissingFields,
        Opt_WarnMissingMethods,
        Opt_WarnDodgyForeignImports,
        Opt_WarnInlineRuleShadowing,
        Opt_WarnUnsupportedLlvmVersion,
        Opt_WarnTabs,
        Opt_WarnUnrecognizedWarningFlags,
        Opt_WarnInaccessibleCode,
        Opt_WarnUnicodeBidirectionalFormatCharacters
      ]

minusWOpts :: [WarningFlag]
minusWOpts
    = standardWarnings ++
      [ Opt_WarnUnusedTopBinds,
        Opt_WarnUnusedLocalBinds,
        Opt_WarnUnusedPatternBinds,
        Opt_WarnUnusedMatches,
        Opt_WarnUnusedForalls,
        Opt_WarnUnusedImports,
        Opt_WarnIncompletePatterns
      ]

minusWallOpts :: [WarningFlag]
minusWallOpts
    = minusWOpts ++
      [ Opt_WarnTypeDefaults,
        Opt_WarnNameShadowing,
        Opt_WarnMissingSignatures,
        Opt_WarnOrphans,
        Opt_WarnIncompleteUniPatterns
      ]

minusWeverythingOpts :: [WarningFlag]
minusWeverythingOpts = [ toEnum 0 .. ]

unusedBindsFlags :: [WarningFlag]
unusedBindsFlags = [ Opt_WarnUnusedTopBinds
                   , Opt_WarnUnusedLocalBinds
                   , Opt_WarnUnusedPatternBinds
                   ]
