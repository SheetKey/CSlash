{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}

module CSlash.Tc.Errors.Types where

import CSlash.Cs
-- import GHC.Tc.Errors.Types.PromotionErr
-- import GHC.Tc.Errors.Hole.FitTypes (HoleFit)
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Evidence (TyCoBindsVar, KiCoBindsVar)
import CSlash.Tc.Types.Origin ( CtOrigin (), SkolemInfoAnon (SigSkol)
                              , InstanceWhat, KindedThing )
-- import GHC.Tc.Types.Rank (Rank)
import CSlash.Tc.Utils.TcType
import CSlash.Types.Basic
import CSlash.Types.Error
import CSlash.Types.Avail
-- import CSlash.Types.Hint (UntickedPromotedThing(..))
-- import GHC.Types.ForeignCall (CLabelString)
-- import GHC.Types.Id.Info ( RecSelParent(..) )
import CSlash.Types.Name (NamedThing(..), Name, OccName, getSrcLoc, getSrcSpan)
import qualified CSlash.Types.Name.Occurrence as OccName
import CSlash.Types.Name.Reader
-- import GHC.Types.SourceFile (HsBootOrSig(..))
import CSlash.Types.SrcLoc
import CSlash.Types.TyThing (TyThing)
import CSlash.Types.Var (Id, {-TyCoVar,-} TyVar, KiVar, AnyTyVar, AnyKiVar {-, TcTyVar, CoVar, Specificity-})
import CSlash.Types.Var.Env (AnyTidyEnv)
import CSlash.Types.Var.Set (TyVarSet, VarSet)
import CSlash.Unit.Types (Module)
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
-- import GHC.Core.Class (Class, ClassMinimalDef, ClassOpItem, ClassATItem)
-- import GHC.Core.Coercion (Coercion)
-- import GHC.Core.Coercion.Axiom (CoAxBranch)
import CSlash.Core.ConLike (ConLike)
import CSlash.Core.DataCon (DataCon{-, FieldLabel-})
-- import GHC.Core.FamInstEnv (FamInst)
-- import GHC.Core.InstEnv (LookupInstanceErrReason, ClsInst, DFunId)
-- import GHC.Core.PatSyn (PatSyn)
import CSlash.Core.Predicate
import CSlash.Core.TyCon (TyCon{-, Role, FamTyConFlav-}, AlgTyConRhs)
import CSlash.Core.Type (Type{-, ThetaType, PredType, ErrorMsgType-}, ForAllFlag)
import CSlash.Core.Kind
import CSlash.Driver.Backend (Backend)
import CSlash.Unit.State (UnitState)
import CSlash.Utils.Misc (filterOut)
-- import qualified GHC.LanguageExtensions as LangExt
import CSlash.Data.FastString (FastString)
-- import GHC.Data.Pair
import GHC.Exception.Type (SomeException)

import qualified Data.List.NonEmpty as NE
import           Data.Typeable (Typeable)
import CSlash.Unit.Module.Warnings (WarningCategory, WarningTxt)

import GHC.Generics ( Generic )
import CSlash.Types.Name.Env (NameEnv)
import CSlash.Iface.Errors.Types
import CSlash.Unit.Module.ModIface (ModIface)
-- import GHC.Tc.Types.TH
import CSlash.Tc.Types.BasicTypes

data TcRnMessageOpts = TcRnMessageOpts
  { tcOptsShowContext :: !Bool
  , tcOptsIfaceOpts :: !IfaceMessageOpts
  }

data ErrInfo = ErrInfo
  { errInfoContext :: !SDoc
  , errInfoSupplementary :: !SDoc
  }

data TcRnMessageDetailed = TcRnMessageDetailed !ErrInfo !TcRnMessage
  deriving Generic

data TcRnMessage where
  TcRnUnknownMessage :: (UnknownDiagnostic (DiagnosticOpts TcRnMessage)) -> TcRnMessage
  TcRnMessageWithInfo :: !UnitState -> !TcRnMessageDetailed -> TcRnMessage
  TcRnSolverReport :: SolverReportWithCtxt -> DiagnosticReason -> TcRnMessage
  TcRnBindingOfExistingName :: RdrName -> TcRnMessage
  TcRnQualifiedBinder :: !RdrName -> TcRnMessage
  TcRnMultipleFixityDecls :: SrcSpan -> RdrName -> TcRnMessage
  TcRnDuplicateDecls :: !OccName -> !(NE.NonEmpty Name) -> TcRnMessage
  TcRnUnusedName :: !OccName -> !UnusedNameProv -> TcRnMessage
  TcRnModMissingRealSrcSpan :: Module -> TcRnMessage
  TcRnImplicitImportOfPrelude :: TcRnMessage
  TcRnTypeSynonymCycle :: !TySynCycleTyCons -> TcRnMessage
  TcRnInterfaceError :: !IfaceMessage -> TcRnMessage
  TcRnSelfImport :: !ModuleName -> TcRnMessage
  TcRnNoExplicitImportList :: !ModuleName -> TcRnMessage
  TcRnDodgyImports :: !DodgyImportsReason -> TcRnMessage
  TcRnMissingImportList :: IE Ps -> TcRnMessage
  TcRnImportLookup :: !ImportLookupReason -> TcRnMessage
  TcRnNotInScope :: NotInScopeError -> RdrName -> [ImportError] -> [CsHint] -> TcRnMessage
  TcRnMatchesHaveDiffNumArgs :: !CsMatchContextRn -> !MatchArgBadMatches -> TcRnMessage
  TcRnShadowedName :: OccName -> ShadowedNameProvenance -> TcRnMessage
  TcRnSimplifierTooManyIterations :: KiCts -> !IntWithInf -> WantedKiConstraints -> TcRnMessage
  TcRnBindingNameConflict :: !RdrName -> !(NE.NonEmpty SrcSpan) -> TcRnMessage
  TcRnTyThingUsedWrong :: !WrongThingSort -> !TcTyKiThing -> !Name -> TcRnMessage
  TcRnArityMismatch :: !(TyThing (AnyTyVar AnyKiVar) AnyKiVar) -> !Arity -> !Arity -> TcRnMessage
  deriving Generic

data ShadowedNameProvenance
  = ShadowedNameProvenanceLocal !SrcLoc
  | ShadowedNameProvenanceGlobal [GlobalRdrElt]

data SolverReport = SolverReport
  { sr_important_msg :: SolverReportWithCtxt
  , sr_supplementary :: [SolverReportSupplementary]
  }

data SolverReportSupplementary
  = SupplementaryBindings RelevantBindings
  | SupplementaryHoleFits ValidHoleFits
  | SupplementaryCts [(AnyPredKind, RealSrcSpan)]

data SolverReportWithCtxt = SolverReportWithCtxt
  { reportContext :: SolverReportErrCtxt
  , reportContent :: TcSolverReportMsg
  }
  deriving Generic

data SolverReportErrCtxt = CEC
  { cec_tencl :: [TyImplication]
  , cec_kencl :: [KiImplication]
  , cec_tidy :: AnyTidyEnv
  , cec_ty_binds :: TyCoBindsVar
  , cec_ki_binds :: KiCoBindsVar
  , cec_defer_type_errors :: DiagnosticReason
  , cec_expr_holes :: DiagnosticReason
  , cec_out_of_scope_holes :: DiagnosticReason
  , cec_warn_redundant :: Bool
  , cec_suppress :: Bool
  , cec_expand_syns :: Bool
  }

getUserGivens :: SolverReportErrCtxt -> [KiImplication]
getUserGivens (CEC { cec_kencl = implics }) = getUserGivensFromImplics implics

----------------------------------------------------------------------------
--
--   ErrorItem
--
----------------------------------------------------------------------------

data ErrorItem
  = KEI
    { ei_ki_pred :: AnyPredKind
    , ei_ki_evdest :: Maybe (KindCoercionHole AnyKiVar)
    , ei_flavor :: CtFlavor
    , ei_loc :: CtLoc
    , ei_m_reason :: Maybe CtIrredReason
    , ei_suppress :: Bool
    }
  | TEI
    { ei_ty_pred :: AnyPredType
    , ei_ty_evdest :: Maybe AnyTypeCoercionHole
    , ei_flavor :: CtFlavor
    , ei_loc :: CtLoc
    , ei_m_reason :: Maybe CtIrredReason
    , ei_suppress :: Bool
    }

instance Outputable ErrorItem where
  ppr (KEI { ei_ki_pred = pred
           , ei_ki_evdest = m_evdest
           , ei_flavor = flav
           , ei_suppress = supp })
    = pp_supp <+> ppr flav <+> pp_dest m_evdest <+> ppr pred
    where
      pp_dest Nothing = empty
      pp_dest (Just ev) = ppr ev <+> colon

      pp_supp = if supp then text "suppress:" else empty
  ppr (TEI { ei_ty_pred = pred
           , ei_ty_evdest = m_evdest
           , ei_flavor = flav
           , ei_suppress = supp })
    = pp_supp <+> ppr flav <+> pp_dest m_evdest <+> ppr pred
    where
      pp_dest Nothing = empty
      pp_dest (Just ev) = ppr ev <+> colon

      pp_supp = if supp then text "suppress:" else empty

errorItemOrigin :: ErrorItem -> CtOrigin
errorItemOrigin = ctLocOrigin . ei_loc

errorItemCtLoc :: ErrorItem -> CtLoc
errorItemCtLoc = ei_loc

errorItemHasAmbigs :: ErrorItem -> Bool
errorItemHasAmbigs (KEI { ei_ki_pred = pred })
  = let ambig_kvs = ambigKvsOfKi pred
    in not (null ambig_kvs)
errorItemHasAmbigs (TEI { ei_ty_pred = pred })
  = let ambig_tvs = panic "ambigTvsOfTy pred"
    in panic "not (null ambig_tvs)"

errorItemExtraNote :: ErrorItem -> SDoc
errorItemExtraNote (KEI { ei_ki_pred = pred })
  = let (_, k1, k2) = getPredKis pred
    in if any isMonoFunKi [k1, k2]
       then text "(maybe you haven't applied a type function to enough arguments?)"
       else empty
errorItemExtraNote (TEI { ei_ty_pred = pred })
  = let (t1, t2) = getPredTys pred
    in panic "errorItemExtraNote"

solverCtxtMismatchMsg :: SolverReportErrCtxt -> ErrorItem -> MismatchMsg
solverCtxtMismatchMsg (CEC { cec_kencl = implics }) item@(KEI {})
  = let useful_givens = getUserGivensFromImplics implics
    in CouldNotDeduceKi useful_givens (item NE.:| []) Nothing
solverCtxtMismatchMsg (CEC { cec_tencl = implics }) item@(TEI {})
  = let useful_givens = getUserGivensFromImplics implics
    in CouldNotDeduceTy useful_givens (item NE.:| []) Nothing

data TcSolverReportMsg
  = CannotUnifyKiVariable
    { mismatchMsg :: MismatchMsg
    , cannotUnifyReason :: CannotUnifyKiVariableReason
    }
  | Mismatch
    { mismatchMsg :: MismatchMsg
    , mismatchKiVarInfo :: Maybe KiVarInfo
    , mismatchAmbiguityInfo :: [AmbiguityInfo]
    }
  | CannotResolveRelation
    { cannotResolve_item :: ErrorItem
    , cannotResolve_relevant_bindings :: RelevantBindings
    }
  deriving Generic

data MismatchMsg
  = BasicMismatch
    { mismatch_ea :: MismatchEA
    , mismatch_item :: ErrorItem
    , mismatch_ki1 :: AnyMonoKind
    , mismatch_ki2 :: AnyMonoKind
    , mismatch_whenMatching :: Maybe WhenMatching
    , mismatch_mb_same_kicon :: Maybe SameKiConInfo
    }
  | KindEqMismatch
    { keq_mismatch_item :: ErrorItem
    , keq_mismatch_ki1 :: AnyMonoKind
    , keq_mismatch_ki2 :: AnyMonoKind
    , keq_mismatch_expected :: AnyMonoKind
    , keq_mismatch_actual :: AnyMonoKind
    , keq_mismatch_what :: Maybe KindedThing
    , keq_mb_same_kicon :: Maybe SameKiConInfo
    }
  | CouldNotDeduceTy
    { cnd_user_ty_givens :: [TyImplication]
    , cnd_wanted :: NE.NonEmpty ErrorItem
    , cnd_extra :: Maybe CND_Extra
    }
  | CouldNotDeduceKi
    { cnd_user_ki_givens :: [KiImplication]
    , cnd_wanted :: NE.NonEmpty ErrorItem
    , cnd_extra :: Maybe CND_Extra
    }
  deriving Generic

data MismatchEA
  = NoEA

data CannotUnifyKiVariableReason
  = CannotUnifyWithPolykind ErrorItem AnyKiVar AnyMonoKind (Maybe KiVarInfo)
  | OccursCheck { occursCheckAmbiguityInfos :: [AmbiguityInfo] }
  | DifferentKiVars KiVarInfo
  deriving Generic


data CND_Extra = CND_Extra TypeOrKind AnyMonoKind AnyMonoKind

data KiVarInfo = KiVarInfo
  { thisKiVar :: AnyKiVar
  , thisKiVarIsUntouchable :: Maybe KiImplication
  , otherKi :: Maybe AnyKiVar
  }

data SameKiConInfo
  = SameKiCon BuiltInKi
  | SameFunKi

data AmbiguityInfo = Ambiguity

data ExpectedActualInfo

data WhenMatching = WhenMatching AnyMonoKind AnyMonoKind CtOrigin (Maybe TypeOrKind)
  deriving Generic

data BadImportKind
  = BadImportNotExported [CsHint]
  | BadImportAvailTyCon
  | BadImportAvailDataCon OccName
  | BadImportNotExportedSubordinates [OccName]
  | BadImportAvailVar
  deriving Generic

data NotInScopeError
  = NotInScope
  | NoExactName Name
  | SameName [GlobalRdrElt]
  | MissingBinding SDoc [CsHint]
  | NoTopLevelBinding
  | NotInScopeTc (NameEnv TcTyKiThing)
  deriving Generic

mkTcRnNotInScope :: RdrName -> NotInScopeError -> TcRnMessage
mkTcRnNotInScope rdr err = TcRnNotInScope err rdr [] noHints

data HoleFitDispConfig = HFDC

data ImportError
  = MissingModule ModuleName
  | ModulesDoNotExport (NE.NonEmpty Module) OccName

data FitsMbSuppressed = Fits
  -- { fits :: [HoleFit]
  -- , fitSuppressed :: Bool
  -- }

data ValidHoleFits = ValidHoleFits
  { holeFits :: FitsMbSuppressed
  , refinementFits :: FitsMbSuppressed
  }

data RelevantBindings = RelevantBindings
  { relevantBindingNamesAndKis :: [(Name, AnyKind)]
  , ranOutOfFuel :: Bool
  }

pprRelevantBindings :: RelevantBindings -> SDoc
pprRelevantBindings (RelevantBindings bds ran_out_of_fuel)
  = ppUnless (null rel_bds)
    $ hang (text "Relevant bindings include")
      2 (vcat (map ppr_binding rel_bds) $$ ppWhen ran_out_of_fuel discardMsg)
  where
    ppr_binding (nm, tidy_ki) = sep [ pprPrefixOcc nm <+> colon <+> ppr tidy_ki
                                    , nest 2 (parens (text "bound at" <+> ppr (getSrcLoc nm))) ]
    rel_bds = filter (not . isGeneratedSrcSpan . getSrcSpan . fst) bds

discardMsg :: SDoc
discardMsg = text "(Some bindings suppressed;" <+>
             text "use -fmax-relevant-binds=N or -fno-max-relevant-binds)"

{- *********************************************************************
*                                                                      *
      Context for renaming errors
*                                                                      *
********************************************************************* -}

data CsDocContext
  = TypeSigCtx SDoc
  | TySynCtx (LocatedN RdrName)
  | PatCtx
  | ExprWithTySigCtx
  | CsTypeCtx

data MatchArgBadMatches where
  MatchArgMatches :: { matchArgFirstMatch :: LocatedA (Match Rn body)
                     , matchArgBadMatches :: NE.NonEmpty (LocatedA (Match Rn body)) }
                  -> MatchArgBadMatches

data WrongThingSort
  = WrongThingType
  | WrongThingKind

type TySynCycleTyCons = [Either (TyCon (TyVar KiVar) KiVar) (LCsBind Rn)]

data DodgyImportsReason
  = DodgyImportsEmptyParent !GlobalRdrElt
  | DodgyImportsHiding !ImportLookupReason
  deriving Generic

data ImportLookupReason where
  ImportLookupBad :: BadImportKind -> ModIface -> ImpDeclSpec -> IE Ps -> ImportLookupReason
  ImportLookupQualified :: !RdrName -> ImportLookupReason
  ImportLookupIllegal :: ImportLookupReason
  ImportLookupAmbiguous :: !RdrName -> ![GlobalRdrElt] -> ImportLookupReason
  deriving Generic

data UnusedNameProv
  = UnusedNameTopDecl
  | UnusedNameImported !ModuleName
  | UnusedNameTypePattern
  | UnusedNameMatch
  | UnusedNameLocalBind
