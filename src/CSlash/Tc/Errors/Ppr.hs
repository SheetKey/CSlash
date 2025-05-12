{-# LANGUAGE TypeApplications #-}
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
import CSlash.Tc.Types.BasicTypes
import CSlash.Tc.Types.Constraint
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

import CSlash.Iface.Errors.Types
import CSlash.Iface.Errors.Ppr
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
                                         , tcOptsIfaceOpts = defaultDiagnosticOpts @IfaceMessage }

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
    TcRnSolverReport msg _ -> mkSimpleDecorated $ pprSolverReportWithCtxt msg
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
    TcRnTypeSynonymCycle bind_or_tcs -> mkSimpleDecorated $
      sep [ text "Cycle in type synonym declarations:"
          , nest 2 (vcat (map ppr_bind bind_or_tcs)) ]
      where
        ppr_bind = \case
          Right (L loc bind) -> ppr (locA loc) <> colon <+> ppr bind
          Left tc -> let n = tyConName tc
                     in ppr (getSrcSpan n) <> colon <+> ppr n <+> text "from external module"
    TcRnInterfaceError reason ->
      diagnosticMessage (tcOptsIfaceOpts opts) reason
    TcRnSelfImport imp_mod_name -> mkSimpleDecorated $
      text "A module cannot import itself:" <+> ppr imp_mod_name
    TcRnNoExplicitImportList mod -> mkSimpleDecorated $
      text "The module" <+> quotes (ppr mod) <+> text "does not have an explicit import list"
    TcRnDodgyImports d -> case d of
      DodgyImportsEmptyParent gre -> mkDecorated $
        [dodgy_msg (text "import") gre (dodgy_msg_insert gre)]
      DodgyImportsHiding reason -> mkSimpleDecorated $
        pprImportLookup reason
    TcRnMissingImportList ie -> mkDecorated
      [ text "The import item" <+> quotes (ppr ie)
        <+> text "does not have ann explicit import list" ]
    TcRnImportLookup reason -> mkSimpleDecorated $
      pprImportLookup reason
    TcRnNotInScope err name imp_errs _ -> mkSimpleDecorated $
      pprScopeError name err $$ vcat (map ppr imp_errs)
    TcRnShadowedName occ provenance ->
      let shadowed_locs = case provenance of
            ShadowedNameProvenanceLocal n -> [text "bound at" <+> ppr n]
            ShadowedNameProvenanceGlobal gres -> map pprNameProvenance gres
      in mkSimpleDecorated $
         sep [ text "This binding for" <+> quotes (ppr occ)
               <+> text "shadows the existing binding" <> plural shadowed_locs
             , nest 2 (vcat shadowed_locs) ]
    TcRnSimplifierTooManyIterations simples limit wc -> mkSimpleDecorated $
      hang (text "solveWanteds: too many iterations"
            <+> parens (text "limit =" <+> ppr wc))
           2 (vcat [ text "Unsolved:" <+> ppr wc
                   , text "Simples:" <+> ppr simples ])
    TcRnBindingNameConflict name locs -> mkSimpleDecorated $
      vcat [ text "Conflicting definitions for" <+> quotes (ppr name)
           , locations ]
      where
        locations = text "Bound at:" <+> vcat (map ppr (sortBy leftmost_smallest (NE.toList locs)))
    TcRnTyThingUsedWrong sort thing name -> mkSimpleDecorated $
      pprTyThingUsedWrong sort thing name
    TcRnArityMismatch thing thing_arity nb_args -> mkSimpleDecorated $
      hsep [ text "The" <+> what, quotes (ppr $ getName thing)
           , text "should have"
           , n_arguments <> comma
           , text "but has been given"
           , if nb_args == 0 then text "none" else int nb_args ]

      where
        what = case thing of
                 ATyCon tc -> ppr (tyConFlavor tc)
                 _ -> text (tyThingCategory thing)
        n_arguments | thing_arity == 0 = text "no arguments"
                    | thing_arity == 1 = text "1 argument"
                    | otherwise = hsep [int thing_arity, text "arguments"]

  diagnosticReason = \case
    TcRnUnknownMessage m -> diagnosticReason m
    TcRnMessageWithInfo _ (TcRnMessageDetailed _ m) -> diagnosticReason m
    TcRnSolverReport _ reason -> reason
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
    TcRnTypeSynonymCycle{} -> ErrorWithoutFlag
    TcRnInterfaceError err -> interfaceErrorReason err
    TcRnSelfImport{} -> ErrorWithoutFlag
    TcRnNoExplicitImportList{} -> WarningWithFlag Opt_WarnMissingImportList
    TcRnDodgyImports{} -> WarningWithFlag Opt_WarnDodgyImports
    TcRnMissingImportList{} -> WarningWithFlag Opt_WarnMissingImportList
    TcRnImportLookup{} -> ErrorWithoutFlag
    TcRnNotInScope{} -> ErrorWithoutFlag
    TcRnShadowedName{} -> WarningWithFlag Opt_WarnNameShadowing
    TcRnSimplifierTooManyIterations{} -> ErrorWithoutFlag
    TcRnBindingNameConflict{} -> ErrorWithoutFlag
    TcRnTyThingUsedWrong{} -> ErrorWithoutFlag
    TcRnArityMismatch{} -> ErrorWithoutFlag

  diagnosticHints = \case
    TcRnUnknownMessage m -> diagnosticHints m
    TcRnMessageWithInfo _ (TcRnMessageDetailed _ m) -> diagnosticHints m
    TcRnSolverReport (SolverReportWithCtxt ctxt msg) _ -> tcSolverReportMsgHints ctxt msg
    TcRnBindingOfExistingName{} -> noHints
    TcRnQualifiedBinder{} -> noHints
    TcRnMultipleFixityDecls{} -> noHints
    TcRnDuplicateDecls{} -> noHints
    TcRnUnusedName{} -> noHints
    TcRnModMissingRealSrcSpan{} -> noHints
    TcRnImplicitImportOfPrelude{} -> noHints
    TcRnTypeSynonymCycle{} -> noHints
    TcRnInterfaceError reason -> interfaceErrorHints reason
    TcRnSelfImport{} -> noHints
    TcRnNoExplicitImportList{} -> noHints
    TcRnDodgyImports{} -> noHints
    TcRnMissingImportList{} -> noHints
    TcRnImportLookup (ImportLookupBad k _ is ie) ->
      let mod_name = moduleName $ is_mod is
          occ = rdrNameOcc $ ieName ie
      in case k of
           BadImportAvailVar -> [ImportSuggestion occ $ CouldRemoveTypeKeyword mod_name]
           BadImportNotExported suggs -> suggs
           BadImportAvailTyCon -> [ImportSuggestion occ $ CouldAddTypeKeyword mod_name]
           BadImportAvailDataCon par -> [ImportSuggestion occ $
                                         ImportDataCon (Just mod_name) par]
           BadImportNotExportedSubordinates{} -> noHints
    TcRnImportLookup{} -> noHints
    TcRnNotInScope err _ _ hints -> scopeErrorHints err ++ hints
    TcRnShadowedName{} -> noHints
    TcRnSimplifierTooManyIterations{} -> [SuggestIncreasedSimplifierIterations]
    TcRnBindingNameConflict{} -> noHints
    TcRnTyThingUsedWrong{} -> noHints
    TcRnArityMismatch{} -> noHints

  diagnosticCode = constructorCode

messageWithInfoDiagnosticMessage
  :: UnitState -> ErrInfo -> Bool -> DecoratedSDoc -> DecoratedSDoc
messageWithInfoDiagnosticMessage unit_state ErrInfo{..} show_ctxt important =
  let err_info' = map (pprWithUnitState unit_state)
                      ([errInfoContext | show_ctxt] ++ [errInfoSupplementary])
  in (mapDecoratedSDoc (pprWithUnitState unit_state) important) `unionDecoratedSDoc`
     mkDecorated err_info'

dodgy_msg :: Outputable ie => SDoc -> GlobalRdrElt -> ie -> SDoc
dodgy_msg kind tc ie = panic "dodgy_msg"

dodgy_msg_insert :: GlobalRdrElt -> IE Rn
dodgy_msg_insert tc_gre = panic "dodgy_msg_insert"

{- *********************************************************************
*                                                                      *
              Outputable SolverReportErrCtxt (for debugging)
*                                                                      *
**********************************************************************-}

instance Outputable SolverReportErrCtxt where
  ppr _ = panic "Outputable SolverReportErrCtxt"

{- *********************************************************************
*                                                                      *
                    Outputting TcSolverReportMsg errors
*                                                                      *
**********************************************************************-}

pprSolverReportWithCtxt :: SolverReportWithCtxt -> SDoc
pprSolverReportWithCtxt _ = panic "pprSolverReportWithCtxt"

{- *********************************************************************
*                                                                      *
      Outputting ScopeError messages
*                                                                      *
********************************************************************* -}

pprScopeError :: RdrName -> NotInScopeError -> SDoc
pprScopeError rdr_name scope_err = case scope_err of
  NotInScope -> hang (text "Not in scope:") 2 (what <+> quotes (ppr rdr_name))
  NoExactName name -> text "The Name" <+> quotes (ppr name) <+> text "is not in scope."
  SameName gres ->
    assertPpr (length gres >= 2) (text "pprScopeError SameName: fewer than 2 elements"
                                  $$ nest 2 (ppr gres))
    $ hang (text "Same Name in multiple name-spaces:") 2 (vcat (map pp_one sorted_names))
    where
      sorted_names = sortBy (leftmost_smallest `on` nameSrcSpan)
                     $ map greName gres
      pp_one name = hang (pprNameSpace (occNameSpace (getOccName name))
                          <+> quotes (ppr name) <> comma)
                    2 (text "declared at:" <+> ppr (nameSrcLoc name))
  MissingBinding thing _ -> sep [ text "The" <+> thing <+> text "for" <+> quotes (ppr rdr_name)
                                , nest 2 $ text "lacks an accompanying binding" ]
  NoTopLevelBinding -> hang (text "No top-level binding for")
                       2 (what <+> quotes (ppr rdr_name) <+> text "in this module")
  NotInScopeTc env ->
    vcat [ text "CSL internal error:" <+> quotes (ppr rdr_name)
           <+> text "is not in scope during type checking, but it passed the renamer"
         , text "tcl_env of environment:" <+> ppr env ]
  where
    what = pprNonVarNameSpace (occNameSpace (rdrNameOcc rdr_name))

scopeErrorHints :: NotInScopeError -> [CsHint]
scopeErrorHints scope_err = case scope_err of
  MissingBinding _ hints -> hints
  _ -> noHints

tcSolverReportMsgHints :: SolverReportErrCtxt -> TcSolverReportMsg -> [CsHint]
tcSolverReportMsgHints ctxt _ = panic "tcSolverReportMsgHints"

{- *********************************************************************
*                                                                      *
      Outputting ImportError messages
*                                                                      *
********************************************************************* -}

instance Outputable ImportError where
  ppr _ = panic "ppr ImportError"

{- *********************************************************************
*                                                                      *
      Contexts for renaming errors
*                                                                      *
********************************************************************* -}

pprCsDocContext :: CsDocContext -> SDoc
pprCsDocContext (TypeSigCtx doc) = text "the type signature for" <+> doc
pprCsDocContext (TySynCtx name) = text "the declaration for type synonym" <+> quotes (ppr name)
pprCsDocContext PatCtx = text "a pattern type-signature"
pprCsDocContext ExprWithTySigCtx = text "an expression type signature"
pprCsDocContext CsTypeCtx = text "a type argument"

pprTyThingUsedWrong :: WrongThingSort -> TcTyKiThing -> Name -> SDoc
pprTyThingUsedWrong sort thing name =
  pprTcTyKiThingCategory thing <+> quotes (ppr name) <+>
  text "used as a" <+> pprWrongThingSort sort

pprWrongThingSort :: WrongThingSort -> SDoc
pprWrongThingSort = text . \case
  WrongThingType -> "type"
  WrongThingKind -> "kind"

pprImportLookup :: ImportLookupReason -> SDoc
pprImportLookup _ = panic "pprImportLookup"

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
