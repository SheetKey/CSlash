{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE GADTs #-}

module CSlash.Tc.Errors.Types where

import CSlash.Cs
-- import GHC.Tc.Errors.Types.PromotionErr
-- import GHC.Tc.Errors.Hole.FitTypes (HoleFit)
-- import GHC.Tc.Types.Constraint
-- import GHC.Tc.Types.Evidence (EvBindsVar)
-- import GHC.Tc.Types.Origin ( CtOrigin (ProvCtxtOrigin), SkolemInfoAnon (SigSkol)
--                            , UserTypeCtxt (PatSynCtxt), TyVarBndrs, TypedThing
--                            , FixedRuntimeRepOrigin(..), InstanceWhat )
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
import CSlash.Core.Kind (Kind)
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
-- import CSlash.Iface.Errors.Types
import CSlash.Unit.Module.ModIface (ModIface)
-- import GHC.Tc.Types.TH
-- import GHC.Tc.Types.BasicTypes

data TcRnMessageOpts = TcRnMessageOpts
  { tcOptsShowContext :: !Bool
  , tcOptsIfaceOpts :: !()
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
  deriving Generic
