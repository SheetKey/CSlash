module CSlash.Driver.Flags
  ( GeneralFlag(..)

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
   | Opt_WarnUnrecognisedWarningFlags
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
   | Opt_WarnDeferredTypeErrors
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
  Opt_WarnAutoOrphans                             -> "auto-orphans" :| []
  Opt_WarnTermVariableCapture                     -> "term-variable-capture" :| []
  Opt_WarnDeferredTypeErrors                      -> "deferred-type-errors" :| []
  Opt_WarnDeferredOutOfScopeVariables             -> "deferred-out-of-scope-variables" :| []
  Opt_WarnDeprecatedFlags                         -> "deprecated-flags" :| []
  Opt_WarnEmptyEnumerations                       -> "empty-enumerations" :| []
  Opt_WarnDuplicateConstraints                    -> "duplicate-constraints" :| []
  Opt_WarnRedundantConstraints                    -> "redundant-constraints" :| []
  Opt_WarnDuplicateExports                        -> "duplicate-exports" :| []
  Opt_WarnInaccessibleCode                        -> "inaccessible-code" :| []
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
  Opt_WarnUnrecognisedWarningFlags                -> "unrecognised-warning-flags" :| []
  Opt_WarnPartialFields                           -> "partial-fields" :| []
  Opt_WarnPrepositiveQualifiedModule              -> "prepositive-qualified-module" :| []
  Opt_WarnUnusedPackages                          -> "unused-packages" :| []
  Opt_WarnCompatUnqualifiedImports                -> "compat-unqualified-imports" :| []
  Opt_WarnOperatorWhitespaceExtConflict           -> "operator-whitespace-ext-conflict" :| []
  Opt_WarnOperatorWhitespace                      -> "operator-whitespace" :| []
  Opt_WarnUnicodeBidirectionalFormatCharacters    -> "unicode-bidirectional-format-characters" :| []

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
        Opt_WarnUnrecognisedWarningFlags,
        Opt_WarnInaccessibleCode,
        Opt_WarnOperatorWhitespaceExtConflict,
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
