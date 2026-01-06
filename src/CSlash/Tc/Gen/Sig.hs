module CSlash.Tc.Gen.Sig where

import CSlash.Data.FastString

import CSlash.Driver.DynFlags
import CSlash.Driver.Backend

import CSlash.Cs

import CSlash.Tc.Errors.Types ( TcRnMessage(..) )
import CSlash.Tc.Gen.CsType
import CSlash.Tc.Types
import CSlash.Tc.Solver( pushLevelAndSolveKindCoercionsX, reportUnsolvedKiCos )
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Zonk.Type
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Validity ( checkValidType )
-- import CSlash.Tc.Utils.Unify( tcSkolemise, unifyType )
-- import CSlash.Tc.Utils.Instantiate( topInstantiate, tcInstTypeBndrs )
-- import CSlash.Tc.Utils.Env( tcLookupId )
import CSlash.Tc.Types.Evidence( CsWrapper{-, (<.>) -})
import CSlash.Tc.Types.BasicTypes

-- import CSlash.Core( hasSomeUnfolding )
import CSlash.Core.Type ( typeKind )
import CSlash.Core.Kind
import CSlash.Core.Kind.Compare (eqMonoKind)
-- import CSlash.Core.Type.Rep( mkNakedFunTy )

import CSlash.Types.Var ( TyVar, varKind, binderVars )
import CSlash.Types.Id  ( Id, idName, mkLocalId )
import CSlash.Types.Basic
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.SrcLoc

import CSlash.Builtin.Names( mkUnboundName )
import CSlash.Unit.Module( getModule )

import CSlash.Utils.Misc as Utils ( singleton )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import CSlash.Data.Maybe( orElse, whenIsJust )

import Data.Maybe( mapMaybe )
import qualified Data.List.NonEmpty as NE
import Control.Monad( unless, when )

{- *********************************************************************
*                                                                      *
               Typechecking user signatures
*                                                                      *
********************************************************************* -}

tcTySigs :: TopLevelFlag -> [LSig Rn] -> TcM ([TcId], TcSigFun)
tcTySigs top_level cs_sigs = checkNoErrs $ do
  ty_sigs <- mapAndReportM (tcTySig top_level) cs_sigs

  let poly_ids = completeSigPolyId <$> ty_sigs
      env = mkNameEnv [(tcSigInfoName sig, sig) | sig <- ty_sigs]

  return (poly_ids, lookupNameEnv env)

tcTySig :: TopLevelFlag -> LSig Rn -> TcM TcSigInfo
tcTySig top_level (L loc (TypeSig _ (L _ name) sig_ty)) = setSrcSpanA loc $ do
  sig <- tcUserTypeSig top_level (locA loc) sig_ty (Just name)
  return $ TcIdSig sig

tcTySig _ _ = panic "tcTySig"

tcUserTypeSig :: TopLevelFlag -> SrcSpan -> LCsSigType Rn -> Maybe Name -> TcM TcCompleteSig
tcUserTypeSig top_level loc cs_sig_ty mb_name = do
  sigma_ty <- tcCsSigType ctxt_no_rrc cs_sig_ty
  traceTc "tcuser" (ppr sigma_ty)
  when (isTopLevel top_level) $
    massertPpr ((snd $ splitForAllKiVars $ typeKind sigma_ty) `eqMonoKind` (BIKi UKd))
    $ vcat [ text "tcUserTypeSig bad kind"
           , ppr sigma_ty ]
    
  return $ CSig { sig_bndr = mkLocalId name sigma_ty
                , sig_ctxt = ctxt_rrc
                , sig_loc = loc }
  where
    name = case mb_name of
             Just n -> n
             Nothing -> mkUnboundName (mkVarOccFS (fsLit "<expression>"))

    ctxt_rrc = ctxt_fn (lcsSigTypeContextSpan cs_sig_ty)
    ctxt_no_rrc = ctxt_fn NoRRC

    ctxt_fn rrc = case mb_name of
                    Just n -> FunSigCtxt n rrc
                    Nothing -> ExprSigCtxt rrc

lcsSigTypeContextSpan :: LCsSigType Rn -> ReportRedundantConstraints
lcsSigTypeContextSpan (L _ CsSig { sig_body = sig_ty }) = go sig_ty
  where
    go (L _ (CsQualTy { cst_ctxt = L span _ })) = WantRRC $ locA span
    go (L _ (CsParTy _ cs_ty)) = go cs_ty
    go _ = NoRRC
