{-# LANGUAGE ExistentialQuantification #-}

module CSlash.Types.Hint 
  ( CsHint(..)
  , AvailableBindings(..)
  , InstantiationSuggestion(..)
  , ImportSuggestion(..)
  , HowInScope(..)
  , SimilarName(..)
  , isBareSymbol
  ) where

import CSlash.Language.Syntax.Expr (LCsExpr)
import CSlash.Language.Syntax (LPat, LIdP)

import qualified Data.List.NonEmpty as NE

import CSlash.Unit.Module (ModuleName, Module)
import CSlash.Unit.Module.Imported (ImportedModsVal)
import CSlash.Cs.Extension (Tc, Rn)
import CSlash.Types.Fixity (LexicalFixity(..))
import CSlash.Types.Name (Name, NameSpace, OccName (occNameFS), isSymOcc, nameOccName)
import CSlash.Types.Name.Reader (RdrName (Unqual), ImpDeclSpec)
import CSlash.Types.SrcLoc (SrcSpan)
import CSlash.Types.Basic (Activation, RuleName)
import CSlash.Types.Var
import CSlash.Parser.Errors.Basic
import CSlash.Utils.Outputable
import CSlash.Data.FastString (fsLit, FastString)

import Data.Typeable ( Typeable )

data AvailableBindings
  = NamedBindings  (NE.NonEmpty Name)
  | UnnamedBinding

data CsHint
  = forall a. (Outputable a, Typeable a) => UnknownHint a
  | SuggestUseSpaces
  --  | SuggestUseWhitespaceAfter !OperatorWhitespaceSymbol
  | SuggestUseWhitespaceAround !String !OperatorWhitespaceOccurrence
  | SuggestParentheses
  | SuggestIncreaseMaxPmCheckModels
  | SuggestAddTypeSignatures AvailableBindings
  --  | SuggestAddInlineOrNoInlinePragma !Var !Activation
  | SuggestIncreaseSimplifierIterations
  | SuggestQualifiedAfterModuleName
  --  | SuggestFixOrphanInst { isFamilyInstance :: Maybe FamFlavor }
  | SuggestTypeSignatureRemoveQualifier
  | SuggestAddStandaloneKindSignature Name
  | SuggestMoveToDeclarationSite
      SDoc
      RdrName
  | SuggestSimilarNames RdrName (NE.NonEmpty SimilarName)
  | ImportSuggestion OccName ImportSuggestion
  | SuggestRenameTypeVariable
  | SuggestIncreaseReductionDepth
  --  | SuggestEtaReduceAbsDataTySyn TyCon
  | SuggestAnonymousWildcard
  | SuggestExplicitQuantification RdrName

data InstantiationSuggestion = InstantiationSuggestion !ModuleName !Module

data ImportSuggestion
  = CouldImportFrom (NE.NonEmpty (Module, ImportedModsVal))
  | CouldUnhideFrom (NE.NonEmpty (Module, ImportedModsVal))
  | CouldRemoveTypeKeyword ModuleName
  | CouldAddTypeKeyword ModuleName
  | ImportDataCon
      { ies_suggest_import_from :: Maybe (ModuleName)
      , ies_parent :: OccName }

data HowInScope
  = LocallyBoundAt SrcSpan
  | ImportedBy ImpDeclSpec

data SimilarName
  = SimilarName Name
  | SimilarRdrName RdrName (Maybe HowInScope)

isBareSymbol :: LexicalFixity -> Name -> Bool
isBareSymbol fixity nm
  | isSymOcc (nameOccName nm)
  , Infix <- fixity
  = True
  | otherwise
  = False
