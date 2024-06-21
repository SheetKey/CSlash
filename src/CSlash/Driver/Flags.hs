module CSlash.Driver.Flags
  ( DumpFlag(..)
  , getDumpFlagFrom
  , enabledIfVerbose
  , GeneralFlag(..)
  , Language(..)
  , defaultLanguage
  , optimisationFlags
  , codeGenFlags

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
  , minusWcompatOpts
  , unusedBindsFlags
  ) where

import CSlash.Utils.Outputable

import Control.DeepSeq
import Control.Monad (guard)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Maybe (fromMaybe,mapMaybe)

data DumpFlag
   = Opt_D_dump_llvm
   deriving (Eq, Show, Enum)

getDumpFlagFrom
  :: (a -> Int)
  -> (a -> EnumSet DumpFlag)
  -> DumpFlag -> a -> Bool
getDumpFlagFrom getVerbosity getFlags f x
  =  (f `EnumSet.member` getFlags x)
  || (getVerbosity x >= 4 && enabledIfVerbose f)

data GeneralFlag
   = Opt_DumpToFile
   | Opt_DumpWithWays
   | Opt_D_dump_minimal_imports
   | Opt_DoAnnotationLinting

   | Opt_WarnIsError  
   | Opt_ShowWarnGroups
   | Opt_HideSourcePaths
   deriving (Eq, Show, Enum)

data WarningFlag =
     Opt_WarnDuplicateExports
   | Opt_WarnDuplicateConstraints
   | Opt_WarnRedundantConstraints
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
   | Opt_WarnUnusedForalls
   | Opt_WarnDeprecatedFlags
   | Opt_WarnOrphans
   | Opt_WarnAutoOrphans
   | Opt_WarnIdentities
   | Opt_WarnTabs
   | Opt_WarnDodgyForeignImports
   | Opt_WarnUnsupportedLlvmVersion
   | Opt_WarnInlineRuleShadowing
   | Opt_WarnTypedHoles
   | Opt_WarnPartialTypeSignatures
   | Opt_WarnMissingExportedSignatures
   | Opt_WarnDeferredOutOfScopeVariables
   | Opt_WarnPartialFields                       
   | Opt_WarnMissingExportList
   | Opt_WarnInaccessibleCode
   | Opt_WarnPrepositiveQualifiedModule          
   | Opt_WarnUnusedPackages                      
   | Opt_WarnCompatUnqualifiedImports            
   | Opt_WarnOperatorWhitespaceExtConflict       
   | Opt_WarnOperatorWhitespace                  
   | Opt_WarnMissingKindSignatures               
   | Opt_WarnMissingPolyKindSignatures           
   | Opt_WarnUnicodeBidirectionalFormatCharacters
   | Opt_WarnTermVariableCapture
   deriving (Eq, Ord, Show, Enum, Bounded)

warnFlagNames :: WarningFlag -> NonEmpty String
warnFlagNames wflag = case wflag of
  Opt_WarnAlternativeLayoutRuleTransitional       -> "alternative-layout-rule-transitional" :| []
  Opt_WarnAmbiguousFields                         -> "ambiguous-fields" :| []
  Opt_WarnAutoOrphans                             -> "auto-orphans" :| []
  Opt_WarnTermVariableCapture                     -> "term-variable-capture" :| []
  Opt_WarnCPPUndef                                -> "cpp-undef" :| []
  Opt_WarnUnbangedStrictPatterns                  -> "unbanged-strict-patterns" :| []
  Opt_WarnDeferredTypeErrors                      -> "deferred-type-errors" :| []
  Opt_WarnDeferredOutOfScopeVariables             -> "deferred-out-of-scope-variables" :| []
  Opt_WarnDeprecatedFlags                         -> "deprecated-flags" :| []
  Opt_WarnDerivingDefaults                        -> "deriving-defaults" :| []
  Opt_WarnDerivingTypeable                        -> "deriving-typeable" :| []
  Opt_WarnDodgyExports                            -> "dodgy-exports" :| []
  Opt_WarnDodgyForeignImports                     -> "dodgy-foreign-imports" :| []
  Opt_WarnDodgyImports                            -> "dodgy-imports" :| []
  Opt_WarnEmptyEnumerations                       -> "empty-enumerations" :| []
  Opt_WarnDuplicateConstraints                    -> "duplicate-constraints" :| []
  Opt_WarnRedundantConstraints                    -> "redundant-constraints" :| []
  Opt_WarnDuplicateExports                        -> "duplicate-exports" :| []
  Opt_WarnHiShadows                               -> "hi-shadowing" :| []
  Opt_WarnInaccessibleCode                        -> "inaccessible-code" :| []
  Opt_WarnImplicitPrelude                         -> "implicit-prelude" :| []
  Opt_WarnImplicitKindVars                        -> "implicit-kind-vars" :| []
  Opt_WarnIncompletePatterns                      -> "incomplete-patterns" :| []
  Opt_WarnIncompletePatternsRecUpd                -> "incomplete-record-updates" :| []
  Opt_WarnIncompleteUniPatterns                   -> "incomplete-uni-patterns" :| []
  Opt_WarnInlineRuleShadowing                     -> "inline-rule-shadowing" :| []
  Opt_WarnIdentities                              -> "identities" :| []
  Opt_WarnMissingFields                           -> "missing-fields" :| []
  Opt_WarnMissingImportList                       -> "missing-import-lists" :| []
  Opt_WarnMissingExportList                       -> "missing-export-lists" :| []
  Opt_WarnMissingLocalSignatures                  -> "missing-local-signatures" :| []
  Opt_WarnMissingMethods                          -> "missing-methods" :| []
  Opt_WarnMissingMonadFailInstances               -> "missing-monadfail-instances" :| []
  Opt_WarnSemigroup                               -> "semigroup" :| []
  Opt_WarnMissingSignatures                       -> "missing-signatures" :| []
  Opt_WarnMissingKindSignatures                   -> "missing-kind-signatures" :| []
  Opt_WarnMissingPolyKindSignatures               -> "missing-poly-kind-signatures" :| []
  Opt_WarnMissingExportedSignatures               -> "missing-exported-signatures" :| []
  Opt_WarnMonomorphism                            -> "monomorphism-restriction" :| []
  Opt_WarnNameShadowing                           -> "name-shadowing" :| []
  Opt_WarnNonCanonicalMonadInstances              -> "noncanonical-monad-instances" :| []
  Opt_WarnNonCanonicalMonadFailInstances          -> "noncanonical-monadfail-instances" :| []
  Opt_WarnNonCanonicalMonoidInstances             -> "noncanonical-monoid-instances" :| []
  Opt_WarnOrphans                                 -> "orphans" :| []
  Opt_WarnOverflowedLiterals                      -> "overflowed-literals" :| []
  Opt_WarnOverlappingPatterns                     -> "overlapping-patterns" :| []
  Opt_WarnMissedSpecs                             -> "missed-specialisations" :| ["missed-specializations"]
  Opt_WarnAllMissedSpecs                          -> "all-missed-specialisations" :| ["all-missed-specializations"]
  Opt_WarnSafe                                    -> "safe" :| []
  Opt_WarnTrustworthySafe                         -> "trustworthy-safe" :| []
  Opt_WarnInferredSafeImports                     -> "inferred-safe-imports" :| []
  Opt_WarnMissingSafeHaskellMode                  -> "missing-safe-haskell-mode" :| []
  Opt_WarnTabs                                    -> "tabs" :| []
  Opt_WarnTypeDefaults                            -> "type-defaults" :| []
  Opt_WarnTypedHoles                              -> "typed-holes" :| []
  Opt_WarnPartialTypeSignatures                   -> "partial-type-signatures" :| []
  Opt_WarnUnrecognisedPragmas                     -> "unrecognised-pragmas" :| []
  Opt_WarnMisplacedPragmas                        -> "misplaced-pragmas" :| []
  Opt_WarnUnsafe                                  -> "unsafe" :| []
  Opt_WarnUnsupportedCallingConventions           -> "unsupported-calling-conventions" :| []
  Opt_WarnUnsupportedLlvmVersion                  -> "unsupported-llvm-version" :| []
  Opt_WarnMissedExtraSharedLib                    -> "missed-extra-shared-lib" :| []
  Opt_WarnUntickedPromotedConstructors            -> "unticked-promoted-constructors" :| []
  Opt_WarnUnusedDoBind                            -> "unused-do-bind" :| []
  Opt_WarnUnusedForalls                           -> "unused-foralls" :| []
  Opt_WarnUnusedImports                           -> "unused-imports" :| []
  Opt_WarnUnusedLocalBinds                        -> "unused-local-binds" :| []
  Opt_WarnUnusedMatches                           -> "unused-matches" :| []
  Opt_WarnUnusedPatternBinds                      -> "unused-pattern-binds" :| []
  Opt_WarnUnusedTopBinds                          -> "unused-top-binds" :| []
  Opt_WarnUnusedTypePatterns                      -> "unused-type-patterns" :| []
  Opt_WarnUnusedRecordWildcards                   -> "unused-record-wildcards" :| []
  Opt_WarnRedundantBangPatterns                   -> "redundant-bang-patterns" :| []
  Opt_WarnRedundantRecordWildcards                -> "redundant-record-wildcards" :| []
  Opt_WarnRedundantStrictnessFlags                -> "redundant-strictness-flags" :| []
  Opt_WarnWrongDoBind                             -> "wrong-do-bind" :| []
  Opt_WarnMissingPatternSynonymSignatures         -> "missing-pattern-synonym-signatures" :| []
  Opt_WarnMissingDerivingStrategies               -> "missing-deriving-strategies" :| []
  Opt_WarnSimplifiableClassConstraints            -> "simplifiable-class-constraints" :| []
  Opt_WarnMissingHomeModules                      -> "missing-home-modules" :| []
  Opt_WarnUnrecognisedWarningFlags                -> "unrecognised-warning-flags" :| []
  Opt_WarnStarBinder                              -> "star-binder" :| []
  Opt_WarnStarIsType                              -> "star-is-type" :| []
  Opt_WarnSpaceAfterBang                          -> "missing-space-after-bang" :| []
  Opt_WarnPartialFields                           -> "partial-fields" :| []
  Opt_WarnPrepositiveQualifiedModule              -> "prepositive-qualified-module" :| []
  Opt_WarnUnusedPackages                          -> "unused-packages" :| []
  Opt_WarnCompatUnqualifiedImports                -> "compat-unqualified-imports" :| []
  Opt_WarnInvalidHaddock                          -> "invalid-haddock" :| []
  Opt_WarnOperatorWhitespaceExtConflict           -> "operator-whitespace-ext-conflict" :| []
  Opt_WarnOperatorWhitespace                      -> "operator-whitespace" :| []
  Opt_WarnImplicitLift                            -> "implicit-lift" :| []
  Opt_WarnMissingExportedPatternSynonymSignatures -> "missing-exported-pattern-synonym-signatures" :| []
  Opt_WarnForallIdentifier                        -> "forall-identifier" :| []
  Opt_WarnUnicodeBidirectionalFormatCharacters    -> "unicode-bidirectional-format-characters" :| []
  Opt_WarnGADTMonoLocalBinds                      -> "gadt-mono-local-binds" :| []
  Opt_WarnTypeEqualityOutOfScope                  -> "type-equality-out-of-scope" :| []
  Opt_WarnLoopySuperclassSolve                    -> "loopy-superclass-solve" :| []
  Opt_WarnTypeEqualityRequiresOperators           -> "type-equality-requires-operators" :| []
  Opt_WarnMissingRoleAnnotations                  -> "missing-role-annotations" :| []
  Opt_WarnImplicitRhsQuantification               -> "implicit-rhs-quantification" :| []
  Opt_WarnIncompleteExportWarnings                -> "incomplete-export-warnings" :| []
  Opt_WarnIncompleteRecordSelectors               -> "incomplete-record-selectors" :| []
  Opt_WarnBadlyStagedTypes                        -> "badly-staged-types" :| []
  Opt_WarnInconsistentFlags                       -> "inconsistent-flags" :| []
  Opt_WarnDataKindsTC                             -> "data-kinds-tc" :| []
  Opt_WarnDeprecatedTypeAbstractions              -> "deprecated-type-abstractions" :| []
  Opt_WarnDefaultedExceptionContext               -> "defaulted-exception-context" :| []

data WarningGroup = W_compat
                  | W_unused_binds
                  | W_extended_warnings
                  | W_default
                  | W_extra
                  | W_all
                  | W_everything
  deriving (Bounded, Enum, Eq)

warningGroupName :: WarningGroup -> String
warningGroupName W_compat            = "compat"
warningGroupName W_unused_binds      = "unused-binds"
warningGroupName W_extended_warnings = "extended-warnings"
warningGroupName W_default           = "default"
warningGroupName W_extra             = "extra"
warningGroupName W_all               = "all"
warningGroupName W_everything        = "everything"

warningGroupFlags :: WarningGroup -> [WarningFlag]
warningGroupFlags W_compat            = minusWcompatOpts
warningGroupFlags W_unused_binds      = unusedBindsFlags
warningGroupFlags W_extended_warnings = []
warningGroupFlags W_default           = standardWarnings
warningGroupFlags W_extra             = minusWOpts
warningGroupFlags W_all               = minusWallOpts
warningGroupFlags W_everything        = minusWeverythingOpts

warningGroupIncludesExtendedWarnings :: WarningGroup -> Bool
warningGroupIncludesExtendedWarnings W_compat            = False
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
        Opt_WarnUnrecognisedPragmas,
        Opt_WarnMisplacedPragmas,
        Opt_WarnDuplicateExports,
        Opt_WarnDerivingDefaults,
        Opt_WarnOverflowedLiterals,
        Opt_WarnEmptyEnumerations,
        Opt_WarnAmbiguousFields,
        Opt_WarnMissingFields,
        Opt_WarnMissingMethods,
        Opt_WarnWrongDoBind,
        Opt_WarnUnsupportedCallingConventions,
        Opt_WarnDodgyForeignImports,
        Opt_WarnInlineRuleShadowing,
        Opt_WarnAlternativeLayoutRuleTransitional,
        Opt_WarnUnsupportedLlvmVersion,
        Opt_WarnMissedExtraSharedLib,
        Opt_WarnTabs,
        Opt_WarnUnrecognisedWarningFlags,
        Opt_WarnSimplifiableClassConstraints,
        Opt_WarnStarBinder,
        Opt_WarnStarIsType,
        Opt_WarnInaccessibleCode,
        Opt_WarnSpaceAfterBang,
        Opt_WarnNonCanonicalMonadInstances,
        Opt_WarnNonCanonicalMonoidInstances,
        Opt_WarnOperatorWhitespaceExtConflict,
        Opt_WarnUnicodeBidirectionalFormatCharacters,
        Opt_WarnGADTMonoLocalBinds,
        Opt_WarnBadlyStagedTypes,
        Opt_WarnTypeEqualityRequiresOperators,
        Opt_WarnInconsistentFlags,
        Opt_WarnDataKindsTC,
        Opt_WarnTypeEqualityOutOfScope
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
        Opt_WarnIncompletePatterns,
        Opt_WarnDodgyExports,
        Opt_WarnDodgyImports,
        Opt_WarnUnbangedStrictPatterns
      ]

minusWallOpts :: [WarningFlag]
minusWallOpts
    = minusWOpts ++
      [ Opt_WarnTypeDefaults,
        Opt_WarnNameShadowing,
        Opt_WarnMissingSignatures,
        Opt_WarnHiShadows,
        Opt_WarnOrphans,
        Opt_WarnUnusedDoBind,
        Opt_WarnTrustworthySafe,
        Opt_WarnMissingPatternSynonymSignatures,
        Opt_WarnUnusedRecordWildcards,
        Opt_WarnRedundantRecordWildcards,
        Opt_WarnIncompleteUniPatterns,
        Opt_WarnIncompletePatternsRecUpd,
        Opt_WarnIncompleteExportWarnings
      ]

minusWeverythingOpts :: [WarningFlag]
minusWeverythingOpts = [ toEnum 0 .. ]

minusWcompatOpts :: [WarningFlag]
minusWcompatOpts
    = [ Opt_WarnCompatUnqualifiedImports
      , Opt_WarnImplicitRhsQuantification
      , Opt_WarnDeprecatedTypeAbstractions
      ]

unusedBindsFlags :: [WarningFlag]
unusedBindsFlags = [ Opt_WarnUnusedTopBinds
                   , Opt_WarnUnusedLocalBinds
                   , Opt_WarnUnusedPatternBinds
                   ]
