{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}

module CSlash.Tc.Errors.Ppr where

import Prelude hiding ((<>))

import CSlash.Builtin.Names
-- import GHC.Builtin.Types ( boxedRepDataConTyCon, tYPETyCon, filterCTuple, pretendNameIsInScope )

import CSlash.Types.Name.Reader
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.Warnings

-- import GHC.Core.Coercion
-- import GHC.Core.Unify     ( tcMatchTys )
import CSlash.Core.TyCon
-- import GHC.Core.Class
import CSlash.Core.DataCon
-- import GHC.Core.Coercion.Axiom (CoAxBranch, coAxiomTyCon, coAxiomSingleBranch)
import CSlash.Core.ConLike
-- import GHC.Core.FamInstEnv ( FamInst(..), famInstAxiom, pprFamInst )
-- import GHC.Core.InstEnv
import CSlash.Core.Type.Rep (Type(..))
-- import CSlash.Core.Type.Ppr (pprWithExplicitKindsWhen,
--                              pprSourceTyCon, pprTyVars, pprWithTYPE, pprTyVar, pprTidiedType)
-- import GHC.Core.PatSyn ( patSynName, pprPatSynType )
-- import GHC.Core.Predicate
import CSlash.Core.Type
-- import GHC.Core.FVs( orphNamesOfTypes )
-- import GHC.CoreToIface

import CSlash.Driver.Flags
import CSlash.Driver.Backend
import CSlash.Cs

import CSlash.Tc.Errors.Types
-- import GHC.Tc.Types.BasicTypes
-- import GHC.Tc.Types.Constraint
import CSlash.Tc.Types.Origin hiding ( Position(..) )
-- import GHC.Tc.Types.Rank (Rank(..))
-- import GHC.Tc.Types.TH
import CSlash.Tc.Utils.TcType

import CSlash.Types.Error
import CSlash.Types.Hint
import CSlash.Types.Hint.Ppr () -- Outputable GhcHint
import CSlash.Types.Basic
import CSlash.Types.Error.Codes
import CSlash.Types.Id
-- import CSlash.Types.Id.Info ( RecSelParent(..) )
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Types.SourceFile
import CSlash.Types.SrcLoc
import CSlash.Types.TyThing
-- import GHC.Types.TyThing.Ppr ( pprTyThingInContext )
import CSlash.Types.Unique.Set ( nonDetEltsUniqSet )
import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.Fixity (defaultFixity)

-- import CSlash.Iface.Errors.Types
-- import CSlash.Iface.Errors.Ppr
import CSlash.Iface.Syntax

import CSlash.Unit.State
import CSlash.Unit.Module

import CSlash.Data.Bag
import CSlash.Data.FastString
import CSlash.Data.List.SetOps ( nubOrdBy )
import CSlash.Data.Maybe
-- import GHC.Data.Pair
import CSlash.Settings.Constants (mAX_TUPLE_SIZE{-, mAX_CTUPLE_SIZE-})
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

-- import qualified GHC.LanguageExtensions as LangExt

-- import CSlash.Data.BooleanFormula (pprBooleanFormulaNice)

import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Foldable ( fold )
import Data.Function (on)
import Data.List ( groupBy, sortBy, tails
                 , partition, unfoldr )
import Data.Ord ( comparing )
import Data.Bifunctor

defaultTcRnMessageOpts :: TcRnMessageOpts
defaultTcRnMessageOpts = TcRnMessageOpts { tcOptsShowContext = True
                                         , tcOptsIfaceOpts = () }

instance HasDefaultDiagnosticOpts TcRnMessageOpts where
  defaultOpts = defaultTcRnMessageOpts

instance Diagnostic TcRnMessage where
  type DiagnosticOpts TcRnMessage = TcRnMessageOpts

  diagnosticMessage opts = \case
    TcRnUnknownMessage (UnknownDiagnostic f m) -> diagnosticMessage (f opts) m
    TcRnMessageWithInfo unit_state (TcRnMessageDetailed err_info msg)
      -> messageWithInfoDiagnosticMessage unit_state err_info
           (tcOptsShowContext opts)
           (diagnosticMessage opts msg)
    TcRnBindingOfExistingName name -> mkSimpleDecorated $
      text "Illegal binding of an existing name:" <+> ppr name
    TcRnQualifiedBinder rdr_name -> mkSimpleDecorated $
      text "Qualified name in binding position:" <+> ppr rdr_name
    TcRnMultipleFixityDecls loc rdr_name -> mkSimpleDecorated $
      vcat [ text "Multiple fixity declarations for" <+> quotes (ppr rdr_name)
           , text "also at " <+> ppr loc ]
    TcRnDuplicateDecls name sorted_names -> mkSimpleDecorated $
      vcat [ text "Multiple declarations of" <+> quotes (ppr name)
           , text "Declared at:" <+>
             vcat (NE.toList $ ppr . nameSrcLoc <$> sorted_names) ]
    TcRnUnusedName name reason -> mkSimpleDecorated $
      pprUnusedName name reason
    TcRnModMissingRealSrcSpan mod -> mkDecorated $
      [ text "Module does not have a RealSrcSpan:" <+> ppr mod ]
    TcRnImplicitImportOfPrelude -> mkSimpleDecorated $
      text "Module" <+> quotes (text "Prelude") <+> text "implicitly imported."

  diagnosticReason = \case
    TcRnUnknownMessage m -> diagnosticReason m
    TcRnMessageWithInfo _ (TcRnMessageDetailed _ m) -> diagnosticReason m
    TcRnBindingOfExistingName{} -> ErrorWithoutFlag
    TcRnQualifiedBinder{} -> ErrorWithoutFlag
    TcRnMultipleFixityDecls{} -> ErrorWithoutFlag
    TcRnDuplicateDecls{} -> ErrorWithoutFlag
    TcRnUnusedName _ prov -> WarningWithFlag $ case prov of
      UnusedNameTopDecl -> Opt_WarnUnusedTopBinds
      UnusedNameImported _ -> Opt_WarnUnusedTopBinds
      UnusedNameTypePattern -> Opt_WarnUnusedTypePatterns
      UnusedNameMatch -> Opt_WarnUnusedMatches
      UnusedNameLocalBind -> Opt_WarnUnusedLocalBinds
    TcRnModMissingRealSrcSpan{} -> ErrorWithoutFlag
    TcRnImplicitImportOfPrelude{} -> WarningWithFlag Opt_WarnImplicitPrelude

  diagnosticHints = \case
    TcRnUnknownMessage m -> diagnosticHints m
    TcRnMessageWithInfo _ (TcRnMessageDetailed _ m) -> diagnosticHints m
    TcRnBindingOfExistingName{} -> noHints
    TcRnQualifiedBinder{} -> noHints
    TcRnMultipleFixityDecls{} -> noHints
    TcRnDuplicateDecls{} -> noHints
    TcRnUnusedName{} -> noHints
    TcRnModMissingRealSrcSpan{} -> noHints
    TcRnImplicitImportOfPrelude{} -> noHints

  diagnosticCode = constructorCode

messageWithInfoDiagnosticMessage
  :: UnitState -> ErrInfo -> Bool -> DecoratedSDoc -> DecoratedSDoc
messageWithInfoDiagnosticMessage unit_state ErrInfo{..} show_ctxt important =
  let err_info' = map (pprWithUnitState unit_state)
                      ([errInfoContext | show_ctxt] ++ [errInfoSupplementary])
  in (mapDecoratedSDoc (pprWithUnitState unit_state) important) `unionDecoratedSDoc`
     mkDecorated err_info'

pprUnusedName :: OccName -> UnusedNameProv -> SDoc
pprUnusedName name reason =
  sep [ msg <> colon
      , nest 2 $ pprNonVarNameSpace (occNameSpace name) <+> quotes (ppr name) ]
  where
    msg = case reason of
      UnusedNameTopDecl -> defined
      UnusedNameImported mod -> text "Imported from" <+> quotes (ppr mod) <+> text "but not used"
      UnusedNameTypePattern -> defined <+> text "on the right hand side"
      UnusedNameMatch -> defined
      UnusedNameLocalBind -> defined
    defined = text "Defined but not used"
