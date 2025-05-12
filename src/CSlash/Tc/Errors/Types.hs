{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}

module CSlash.Tc.Errors.Types where

import CSlash.Cs
-- import GHC.Tc.Errors.Types.PromotionErr
-- import GHC.Tc.Errors.Hole.FitTypes (HoleFit)
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Evidence (KiEvBindsVar)
import CSlash.Tc.Types.Origin ( CtOrigin (), SkolemInfoAnon (SigSkol)
                              , InstanceWhat )
-- import GHC.Tc.Types.Rank (Rank)
-- import GHC.Tc.Utils.TcType (TcType, TcSigmaType, TcPredType,
--                             PatersonCondFailure, PatersonCondFailureContext)
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
import CSlash.Types.Var (Id, {-TyCoVar,-} TypeVar{-, TcTyVar, CoVar, Specificity-})
import CSlash.Types.Var.Env (TidyEnv)
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
-- import GHC.Core.Predicate (EqRel, predTypeEqRel)
import CSlash.Core.TyCon (TyCon{-, Role, FamTyConFlav-}, AlgTyConRhs)
import CSlash.Core.Type (Type{-, ThetaType, PredType, ErrorMsgType-}, ForAllTyFlag)
import CSlash.Core.Kind (Kind, PredKind)
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
  TcRnShadowedName :: OccName -> ShadowedNameProvenance -> TcRnMessage
  TcRnSimplifierTooManyIterations :: Cts -> !IntWithInf -> WantedConstraints -> TcRnMessage
  TcRnBindingNameConflict :: !RdrName -> !(NE.NonEmpty SrcSpan) -> TcRnMessage
  TcRnTyThingUsedWrong :: !WrongThingSort -> !TcTyKiThing -> !Name -> TcRnMessage
  TcRnArityMismatch :: !TyThing -> !Arity -> !Arity -> TcRnMessage
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
  | SupplementaryCts [(PredKind, RealSrcSpan)]

data SolverReportWithCtxt = SolverReportWithCtxt
  { reportContext :: SolverReportErrCtxt
  , reportContent :: TcSolverReportMsg
  }
  deriving Generic

data SolverReportErrCtxt = CEC
  { cec_encl :: [Implication]
  , cec_tidy :: TidyEnv
  , cec_binds :: KiEvBindsVar
  , cec_defer_type_errors :: DiagnosticReason
  , cec_expr_holes :: DiagnosticReason
  , cec_out_of_scope_holes :: DiagnosticReason
  , cec_warn_redundant :: Bool
  , cec_suppress :: Bool
  }

----------------------------------------------------------------------------
--
--   ErrorItem
--
----------------------------------------------------------------------------

data ErrorItem = EI
  { ei_pred :: PredKind
  , ei_evdest :: Maybe TcEvDest
  , ei_flavor :: CtFlavor
  , ei_loc :: CtLoc
  , ei_m_reason :: Maybe CtIrredReason
  , ei_suppress :: Bool
  }

instance Outputable ErrorItem where
  ppr (EI { ei_pred = pred
          , ei_evdest = m_evdest
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

errorItemPred :: ErrorItem -> PredKind
errorItemPred = ei_pred

data TcSolverReportMsg
  = BadTelescope
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
  { relevantBindingNamesAndKis :: [(Name, Kind)]
  , ranOutOfFuel :: Bool
  }

pprRelevantBindings :: RelevantBindings -> SDoc
pprRelevantBindings _ = panic "pprRelevantBindings"

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

data WrongThingSort
  = WrongThingType
  | WrongThingKind

type TySynCycleTyCons = [Either TyCon (LCsBind Rn)]

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
