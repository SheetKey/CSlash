{-# LANGUAGE MonadComprehensions #-}
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
import CSlash.Core.Predicate
import CSlash.Core.Type
import CSlash.Core.Type.Tidy
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs
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
import CSlash.Types.Name hiding (varName)
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
    TcRnMissingExportList mod -> mkSimpleDecorated $
      formatExportItemError (text "module" <+> ppr mod) "is missing an export list"
    TcRnImportLookup reason -> mkSimpleDecorated $
      pprImportLookup reason
    TcRnNotInScope err name imp_errs _ -> mkSimpleDecorated $
      pprScopeError name err $$ vcat (map ppr imp_errs)
    TcRnMatchesHaveDiffNumArgs argsContext (MatchArgMatches match1 bad_matches)
      -> mkSimpleDecorated $
         vcat [ pprMatchContextNouns argsContext <+>
                text "have different numbers of arguments"
              , nest 2 (ppr (getLocA match1))
              , nest 2 (ppr (getLocA (NE.head bad_matches))) ]
    TcRnShadowedName occ provenance ->
      let shadowed_locs = case provenance of
            ShadowedNameProvenanceLocal n -> [text "bound at" <+> ppr n]
            ShadowedNameProvenanceGlobal gres -> map pprNameProvenance gres
      in mkSimpleDecorated $
         sep [ text "This binding for" <+> quotes (ppr occ)
               <+> text "shadows the existing binding" <> plural shadowed_locs
             , nest 2 (vcat shadowed_locs) ]
    TcRnSimplifierTooManyIterations simples limit wc -> mkSimpleDecorated $
      hang (text "solveKiWanteds: too many iterations"
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
    TcRnMissingMain explicit_export_list main_mod main_occ -> mkSimpleDecorated $
      text "The" <+> ppMainFn main_occ
      <+> text "is not" <+> defOrExp <+> text "module"
      <+> quotes (ppr main_mod)
      where
        defOrExp | explicit_export_list = text "exported by"
                 | otherwise = text "defined in"

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
    TcRnMissingExportList{} -> WarningWithFlag Opt_WarnMissingExportList
    TcRnImportLookup{} -> ErrorWithoutFlag
    TcRnNotInScope{} -> ErrorWithoutFlag
    TcRnMatchesHaveDiffNumArgs{} -> ErrorWithoutFlag
    TcRnShadowedName{} -> WarningWithFlag Opt_WarnNameShadowing
    TcRnSimplifierTooManyIterations{} -> ErrorWithoutFlag
    TcRnBindingNameConflict{} -> ErrorWithoutFlag
    TcRnTyThingUsedWrong{} -> ErrorWithoutFlag
    TcRnArityMismatch{} -> ErrorWithoutFlag
    TcRnMissingMain{} -> ErrorWithoutFlag

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
    TcRnMissingExportList{} -> noHints
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
    TcRnMatchesHaveDiffNumArgs{} -> noHints
    TcRnShadowedName{} -> noHints
    TcRnSimplifierTooManyIterations{} -> [SuggestIncreasedSimplifierIterations]
    TcRnBindingNameConflict{} -> noHints
    TcRnTyThingUsedWrong{} -> noHints
    TcRnArityMismatch{} -> noHints
    TcRnMissingMain{} -> noHints

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

formatExportItemError :: SDoc -> String -> SDoc
formatExportItemError exportedThing reason = hsep [ text "The export item"
                                                  , quotes exportedThing
                                                  , text reason ]

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
pprSolverReportWithCtxt (SolverReportWithCtxt { reportContext = ctxt, reportContent = msg })
  = pprTcSolverReportMsg ctxt msg

pprTcSolverReportMsg :: SolverReportErrCtxt -> TcSolverReportMsg -> SDoc

pprTcSolverReportMsg ctxt (CannotUnifyKiVariable msg reason)
  = pprMismatchMsg ctxt msg $$ pprCannotUnifyKiVariableReason ctxt reason

pprTcSolverReportMsg ctxt (Mismatch mismatch_msg kv_info ambig_infos)
  = vcat $ [ pprMismatchMsg ctxt mismatch_msg
           , maybe empty (pprKiVarInfo ctxt) kv_info ]
           ++ (map pprAmbiguityInfo ambig_infos)

pprTcSolverReportMsg ctxt@(CEC { cec_tencl = timplics, cec_kencl = kimplics })
                     (CannotResolveRelation item binds)
  = vcat [ no_inst_msg
         , nest 2 extra_note
         , show_fixes ctxt_fixes
         ]
  where
    orig = errorItemOrigin item
    has_ambigs = errorItemHasAmbigs item

    no_inst_msg :: SDoc
    no_inst_msg
      = pprMismatchMsg ctxt $ solverCtxtMismatchMsg ctxt item

    extra_note = errorItemExtraNote item

    ctxt_fixes = case item of
                   TEI {} -> error "pprTcSolverReportMsg"
                   KEI { ei_ki_pred = pred } -> ctxtFixes has_ambigs pred kimplics

pprCannotUnifyKiVariableReason :: SolverReportErrCtxt -> CannotUnifyKiVariableReason -> SDoc
pprCannotUnifyKiVariableReason ctxt (CannotUnifyWithPolykind item kv1 ki2 mb_kv_info)
  = vcat [ (if handleAnyKv (const True) isSkolemVar kv1
            then text "Cannot equate type variable"
            else text "Cannot instantiate unification variable")
           <+> quotes (ppr kv1)
         , hang (text "with a" <+> what <+> text "involving polykinds:") 2 (ppr ki2)
         , maybe empty (pprKiVarInfo ctxt) mb_kv_info ]
  where
    what = text $ levelString $ ctLocTypeOrKind_maybe (errorItemCtLoc item) `orElse` KindLevel

pprCannotUnifyKiVariableReason ctxt (OccursCheck ambig_infos)
  = vcat (map pprAmbiguityInfo ambig_infos)

pprCannotUnifyKiVariableReason ctxt (DifferentKiVars kv_info)
  = pprKiVarInfo ctxt kv_info

pprUntouchableVariable :: AnyKiVar -> KiImplication -> SDoc
pprUntouchableVariable _ _ = panic "pprUntouchableVariable"

pprMismatchMsg :: SolverReportErrCtxt -> MismatchMsg -> SDoc
pprMismatchMsg ctxt (BasicMismatch ea item ki1 ki2 mb_match_txt same_kc_info)
  = vcat [ addArising (errorItemCtLoc item) msg
         , ea_extra
         , maybe empty (pprWhenMatching ctxt) mb_match_txt
         , maybe empty pprSameKiConInfo same_kc_info ]
  where
    msg | isAtomicKi ki1 || isAtomicKi ki2
        = sep [ text herald1 <+> quotes (ppr ki1)
              , nest padding $ text herald2 <+> quotes (ppr ki2) ]
        | otherwise
        = vcat [ text herald1 <> colon <+> ppr ki1
               , nest padding $ text herald2 <> colon <+> ppr ki2 ]

    herald1 = conc [ "Couldn't match"
                   , if want_ea then "expected" else "" ]
    herald2 = conc [ "with"
                   , if want_ea then ("actual " ++ what) else "" ]

    padding = length herald1 - length herald2

    (want_ea, ea_extra) = case ea of
                            NoEA -> (False, empty)

    what = levelString (ctLocTypeOrKind_maybe (errorItemCtLoc item) `orElse` KindLevel)

    conc = foldr1 add_space
    add_space s1 s2 | null s1 = s2
                    | null s2 = s1
                    | otherwise = s1 ++ (' ' : s2)

pprMismatchMsg ctxt (KindEqMismatch item ki1 ki2 exp act mb_thing mb_same_kc)                    
  = addArising ct_loc $ msg $$ maybe empty pprSameKiConInfo mb_same_kc
  where
    msg = vcat [ text "KindeEqMismatch (needs fixing later)"
               , ppr item
               , text "ki1" <+> ppr ki1
               , text "ki2" <+> ppr ki2
               , text "exp" <+> ppr exp
               , text "act" <+> ppr act ]

    ct_loc = errorItemCtLoc item

pprMismatchMsg ctxt (CouldNotDeduceKi useful_givens (item:|others) mb_extra)
  = main_msg $$ case supplementary of
                  Left infos -> vcat (map (pprExpectedActualInfo ctxt) infos)
                  Right other_msg -> pprMismatchMsg ctxt other_msg
  where
    main_msg | null useful_givens = addArising ct_loc (no_instance_msg <+> missing)
             | otherwise = vcat (addArising ct_loc (no_deduce_msg <+> missing)
                                 : pp_givens useful_givens)

    supplementary = case mb_extra of
                      Nothing -> Left []
                      Just (CND_Extra level ki1 ki2)
                        -> mk_supplementary_ea_msg ctxt level ki1 ki2 orig

    ct_loc = errorItemCtLoc item
    orig = ctLocOrigin ct_loc
    wanteds = map ei_ki_pred (item:others)

    no_instance_msg = case wanteds of
                        [wanted] | KiPredApp pred _ _ <- wanted
                                 , pred `elem` [LTKi, LTEQKi]
                                 -> text "No instance for"
                        _ -> text "Could not solve:"

    no_deduce_msg = case wanteds of
                      [_] -> text "Could not deduce"
                      _ -> text "Could not deduce:"

    missing = case wanteds of
                [w] -> quotes (ppr w)
                _ -> ppr wanteds

pprMismatchMsg ctxt (CouldNotDeduceTy {}) = panic "cndty"

{- *********************************************************************
*                                                                      *
             Outputting additional solver report information
*                                                                      *
**********************************************************************-}

pprExpectedActualInfo :: SolverReportErrCtxt -> ExpectedActualInfo -> SDoc
pprExpectedActualInfo _ _ = panic "pprExpectedActualInfo"

pprWhenMatching :: SolverReportErrCtxt -> WhenMatching -> SDoc
pprWhenMatching _ _ = panic "pprWhenMatching"

pprKiVarInfo :: SolverReportErrCtxt -> KiVarInfo -> SDoc
pprKiVarInfo ctxt (KiVarInfo kv1 mb_implic mb_kv2)
  = vcat [ mk_msg kv1
         , maybe empty (pprUntouchableVariable kv1) mb_implic
         , maybe empty mk_msg mb_kv2 ]
  where
    mk_msg kv = handleAnyKv
             (\_ -> pprSkols ctxt [(unkSkolAnon, [kv])])
             (\tckv -> case tcVarDetails tckv of
                 SkolemVar sk_info _ -> pprSkols ctxt [(getSkolemInfo sk_info, [kv])]
                 MetaVar {} -> empty)
             kv

pprAmbiguityInfo :: AmbiguityInfo -> SDoc
pprAmbiguityInfo _ = panic "pprAmbiguityInfo"

pprSameKiConInfo :: SameKiConInfo -> SDoc
pprSameKiConInfo _ = panic "pprSameKiConInfo"

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
tcSolverReportMsgHints ctxt = \case
  CannotUnifyKiVariable mismatch_msg rea
    -> mismatchMsgHints ctxt mismatch_msg ++ cannotUnifyKiVariableHints rea
  Mismatch { mismatchMsg = mismatch_msg }
    -> mismatchMsgHints ctxt mismatch_msg
  CannotResolveRelation {} -> noHints

mismatchMsgHints :: SolverReportErrCtxt -> MismatchMsg -> [CsHint]
mismatchMsgHints ctxt msg
  = maybeToList [ hint | (exp, act) <- mismatchMsg_ExpectedActuals msg
                       , hint <- suggestAddSig ctxt exp act ]

mismatchMsg_ExpectedActuals :: MismatchMsg -> Maybe (AnyMonoKind, AnyMonoKind)
mismatchMsg_ExpectedActuals = \case
  BasicMismatch { mismatch_ki1 = exp, mismatch_ki2 = act } -> Just (exp, act)
  KindEqMismatch { keq_mismatch_expected = exp, keq_mismatch_actual = act } -> Just (exp, act)
  CouldNotDeduceKi { cnd_extra = cnd_extra }
    | Just (CND_Extra _ exp act) <- cnd_extra -> Just (exp, act)
    | otherwise -> Nothing
  CouldNotDeduceTy {} -> panic "CNDTy"

cannotUnifyKiVariableHints :: CannotUnifyKiVariableReason -> [CsHint]
cannotUnifyKiVariableHints = \case
  CannotUnifyWithPolykind {} -> noHints
  OccursCheck {} -> noHints
  DifferentKiVars {} -> noHints

suggestAddSig :: SolverReportErrCtxt -> AnyMonoKind -> AnyMonoKind -> Maybe CsHint
suggestAddSig ctxt ki1 _ = Nothing

{- *********************************************************************
*                                                                      *
      Outputting ImportError messages
*                                                                      *
********************************************************************* -}

instance Outputable ImportError where
  ppr _ = panic "ppr ImportError"

{- *********************************************************************
*                                                                      *
             Suggested fixes for implication constraints
*                                                                      *
**********************************************************************-}

show_fixes :: [SDoc] -> SDoc
show_fixes [] = empty
show_fixes (f:fs) = sep [ text "Possible fix:"
                        , nest 2 (vcat (f : map (text "or" <+>) fs)) ]

ctxtFixes :: Bool -> AnyPredKind -> [KiImplication] -> [SDoc]
ctxtFixes has_ambig_kvs pred implics
  | not has_ambig_kvs
  , isKiVarKcPred pred
  , (skol:skols) <- usefulContext implics pred
  = [sep [ text "add" <+> pprParendMonoKind pred <+> text "to the" <+> text "context of"
         , nest 2 $ ppr_skol skol $$ vcat [ text "or" <+> ppr_skol skol
                                          | skol <- skols ] ] ]
  | otherwise = []
  where
    ppr_skol skol_info = ppr skol_info

usefulContext :: [KiImplication] -> AnyPredKind -> [SkolemInfoAnon]
usefulContext implics pred = go implics
  where
    pred_kvs = varsOfMonoKind pred

    go [] = []
    go (ic:ics)
      | implausible ic = rest
      | otherwise = kic_info ic : rest
      where rest | any ((`elemVarSet` pred_kvs) . toAnyKiVar) (kic_skols ic) = []
                 | otherwise = go ics

    implausible ic
      | null (kic_skols ic) = True
      | implausible_info (kic_info ic) = True
      | otherwise = False

    implausible_info (SigSkol (InfSigCtxt {}) _ _) = True
    implausible_info _ = False

pp_givens :: [KiImplication] -> [SDoc]
pp_givens givens = case givens of
                     [] -> []
                     (g:gs) -> ppr_given (text "from the context:") g
                               : map (ppr_given (text "or from:")) gs
  where
    ppr_given herald implic@(KiImplic { kic_given = gs, kic_info = skol_info })
      = hang (herald <+> pprKiCoVarTheta (mkMinimalBy_Ki kiCoVarPred gs))
        2 (sep [ text "bound by" <+> ppr skol_info
               , text "at" <+> ppr (getCtLocEnvLoc (kic_env implic)) ])

{- *********************************************************************
*                                                                      *
                       CtOrigin information
*                                                                      *
**********************************************************************-}

levelString :: TypeOrKind -> String
levelString TypeLevel = "type"
levelString KindLevel = "kind"

addArising :: CtLoc -> SDoc -> SDoc
addArising ct_loc msg = hang msg 2 (pprArising ct_loc)

pprArising :: CtLoc -> SDoc
pprArising ct_loc
  | suppress_origin = empty
  | otherwise = pprCtOrigin orig
  where
    orig = ctLocOrigin ct_loc
    suppress_origin
      | isGivenOrigin orig = True
      | otherwise = case orig of
          TypeEqOrigin {} -> True
          KindEqOrigin {} -> True
          KindCoOrigin {} -> True
          _ -> False

{- *********************************************************************
*                                                                      *
                           SkolemInfo
*                                                                      *
**********************************************************************-}

tidySkolemInfoAnon :: AnyTidyEnv -> SkolemInfoAnon -> SkolemInfoAnon
tidySkolemInfoAnon env (SigSkol cx ty tv_prs) = tidySigSkol env cx ty tv_prs
tidySkolemInfoAnon env (InferSkol ids) = InferSkol (mapSnd (tidyType env) ids)
tidySkolemInfoAnon env (UnifyForAllSkol ty) = UnifyForAllSkol (tidyType env ty)
tidySkolemInfoAnon _ info = info

tidySigSkol :: AnyTidyEnv -> UserTypeCtxt -> AnyType -> [(Name, AnyTyVar AnyKiVar)] -> SkolemInfoAnon
tidySigSkol env cx ty tv_prs = SigSkol cx (tidy_ty env ty) tv_prs'
  where
    tv_prs' = mapSnd (panic "tidyTyKiVarOcc env") tv_prs
    inst_env = mkNameEnv tv_prs'

    tidy_ty env (ForAllTy (Bndr tv vis) ty) = ForAllTy (Bndr tv' vis) (tidy_ty env' ty)
      where (env', tv') = tidy_tv_bndr env tv

    tidy_ty env ty@(FunTy { ft_arg = arg, ft_res = res })
      = ty { ft_arg = tidyType env arg, ft_res = tidy_ty env res }

    tidy_ty env ty = tidyType env ty

    tidy_tv_bndr :: AnyTidyEnv -> AnyTyVar AnyKiVar -> (AnyTidyEnv, AnyTyVar AnyKiVar)
    tidy_tv_bndr env@(occ_env, subst, ksubst) tv
      | Just tv' <- lookupNameEnv inst_env (varName tv)
      = ((occ_env, extendVarEnv subst tv tv', ksubst), tv')
      | otherwise
      = panic "tidyVarBndr env tv"

pprSkols :: SolverReportErrCtxt -> [(SkolemInfoAnon, [AnyKiVar])] -> SDoc
pprSkols ctxt zonked_ki_vars
  = let tidy_ki_vars = map (bimap (tidySkolemInfoAnon (cec_tidy ctxt)) id) zonked_ki_vars
    in vcat (map pp_one tidy_ki_vars)
  where
    no_msg = text "No skolem info - we could not find the origin of the following variable"
             <+> ppr zonked_ki_vars
             $$ text "This should not happen."

    pp_one (UnkSkol cs, kvs)
      = vcat [ hang (pprQuotedList kvs)
               2 (is_or_are kvs "a" "(rigid, skolem)")
             , nest 2 (text "of unknown origin")
             , nest 2 (text "bound at" <+> ppr (skolsSpan kvs))
             , no_msg
             , prettyCallStackDoc cs ]

    pp_one (skol_info, kvs)
      = vcat [ hang (pprQuotedList kvs)
               2 (is_or_are kvs "a" "rigid" <+> text "bound by")
             , nest 2 (pprSkolInfo skol_info)
             , nest 2 (text "at" <+> ppr (skolsSpan kvs)) ]

    is_or_are [_] article adjective = text "is" <+> text article <+> text adjective
                                      <+> text "kind variable"
    is_or_are _ _ adjective = text "are" <+> text adjective <+> text "kind variables"

skolsSpan :: [AnyKiVar] -> SrcSpan
skolsSpan skol_kvs = foldr1 combineSrcSpans (map getSrcSpan skol_kvs)

{- *********************************************************************
*                                                                      *
                Utilities for expected/actual messages
*                                                                      *
**********************************************************************-}

mk_supplementary_ea_msg
  :: SolverReportErrCtxt
  -> TypeOrKind
  -> AnyMonoKind
  -> AnyMonoKind
  -> CtOrigin
  -> Either [ExpectedActualInfo] MismatchMsg
mk_supplementary_ea_msg _ _ _ _ _ = panic "mk_supplementary_ea_msg"

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
