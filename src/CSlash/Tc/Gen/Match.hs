{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CSlash.Tc.Gen.Match where

import {-# SOURCE #-} CSlash.Tc.Gen.Expr( tcPolyLExpr, tcInferRhoNC, tcCheckMonoExpr )

import CSlash.Rename.Utils ( bindLocalNames )
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.Env
import CSlash.Tc.Gen.Pat
-- import GHC.Tc.Gen.Do
-- import GHC.Tc.Gen.Head( tcCheckId )
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Gen.Bind
import CSlash.Tc.Utils.Unify
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.Evidence
-- import CSlash.Rename.Env ( irrefutableConLikeTc )

import CSlash.Core.Kind
import CSlash.Core.UsageEnv
import CSlash.Core.TyCon

import CSlash.Cs

import CSlash.Builtin.Types
import CSlash.Builtin.Types.Prim

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc

import CSlash.Types.Name
import CSlash.Types.Id
import CSlash.Types.Var
import CSlash.Types.SrcLoc
import CSlash.Types.Basic( VisArity, isDoExpansionGenerated )

import Control.Monad
import Control.Arrow ( second )
import qualified Data.List.NonEmpty as NE
import Data.Maybe (mapMaybe)

{- *********************************************************************
*                                                                      *
            tcLambdaMatches, tcCaseMatches
*                                                                      *
********************************************************************* -}

tcLambdaMatches
  :: CsExpr Rn
  -> MatchGroup Rn (LCsExpr Rn)
  -> [ExpPatType]
  -> ExpSigmaType
  -> TcM (AnyCsWrapper, MatchGroup Tc (LCsExpr Tc))
tcLambdaMatches e matches invis_pat_tys res_ty = do
  arity <- checkArgCounts matches

  let herald = ExpectedFunTyLam e
  (wrapper, r)
    <- matchExpectedFunTys herald GenSigCtxt arity res_ty $ \pat_tys rhs_ty ->
       tcMatches tcBody (invis_pat_tys ++ pat_tys) rhs_ty matches

  return (wrapper, r)

{- *********************************************************************
*                                                                      *
                tcMatch
*                                                                      *
********************************************************************* -}

type TcMatchAltChecker body
  = LocatedA (body Rn) -> ExpRhoType -> TcM (LocatedA (body Tc))

type AnnoBody body
  = ( Outputable (body Rn)
    , Anno (Match Rn (LocatedA (body Rn))) ~ SrcSpanAnnA
    , Anno (Match Tc (LocatedA (body Tc))) ~ SrcSpanAnnA
    , Anno [LocatedA (Match Rn (LocatedA (body Rn)))] ~ SrcSpanAnnL
    , Anno [LocatedA (Match Tc (LocatedA (body Tc)))] ~ SrcSpanAnnL
    , Anno (GRHS Rn (LocatedA (body Rn))) ~ EpAnnCO
    , Anno (GRHS Tc (LocatedA (body Tc))) ~ EpAnnCO
    , Anno (StmtLR Rn Rn (LocatedA (body Rn))) ~ SrcSpanAnnA
    , Anno (StmtLR Tc Tc (LocatedA (body Tc))) ~ SrcSpanAnnA
    )

tcMatches
  :: (AnnoBody body, Outputable (body Tc))
  => TcMatchAltChecker body
  -> [ExpPatType]
  -> ExpRhoType
  -> MatchGroup Rn (LocatedA (body Rn))
  -> TcM (MatchGroup Tc (LocatedA (body Tc)))
tcMatches tc_body pat_tys rhs_ty (MG { mg_alts = L l matches, mg_ext = origin })
  | null matches
  = panic "tcMatches/null matches"

  | otherwise
  = do umatches <- mapM (tcCollectingUsage . tcMatch tc_body pat_tys rhs_ty) matches
       let (usages, matches') = unzip umatches
       tcEmitBindingUsage $ supUEs usages
       pat_tys <- mapM expTypeToType $ filter_out_forall_pat_tys pat_tys

       rhs_ty <- readExpType rhs_ty
       traceTc "tcMatches" (ppr matches' $$ ppr pat_tys $$ ppr rhs_ty)
       return $ MG { mg_alts = L l matches'
                   , mg_ext = MatchGroupTc pat_tys rhs_ty origin }
  where
    filter_out_forall_pat_tys :: [ExpPatType] -> [ExpSigmaType]
    filter_out_forall_pat_tys = mapMaybe match_fun_pat_ty
      where
        match_fun_pat_ty (ExpFunPatTy t) = Just t
        match_fun_pat_ty ExpForAllPatTy{} = Nothing
        match_fun_pat_ty ExpForAllPatKi{} = Nothing

tcMatch
  :: AnnoBody body
  => TcMatchAltChecker body
  -> [ExpPatType]
  -> ExpRhoType
  -> LMatch Rn (LocatedA (body Rn))
  -> TcM (LMatch Tc (LocatedA (body Tc)))
tcMatch tc_body pat_tys rhs_ty match = do
  wrapLocMA (tc_match pat_tys rhs_ty) match
  where
    tc_match pat_tys rhs_ty match@(Match { m_ext = ext
                                         , m_ctxt = ctxt
                                         , m_pats = L l pats
                                         , m_grhss = grhss })
      = add_match_ctxt $ do
        (pats', grhss') <- tcMatchPats ctxt pats pat_tys
                                      $ tcGRHSs ctxt tc_body grhss rhs_ty
        return $ Match { m_ext = ext
                       , m_ctxt = ctxt
                       , m_pats = L l pats'
                       , m_grhss = grhss' }
      where
        add_match_ctxt thing_inside = case ctxt of
          TyLamTyAlt -> panic "tcMatch/TyLamTyAlt"
          LamAlt -> thing_inside
          TyLamAlt -> thing_inside
          _ -> addErrCtxt (pprMatchInCtxt match) thing_inside

tcGRHSs
  :: AnnoBody body
  => CsMatchContextRn
  -> TcMatchAltChecker body
  -> GRHSs Rn (LocatedA (body Rn))
  -> ExpRhoType
  -> TcM (GRHSs Tc (LocatedA (body Tc)))
tcGRHSs ctxt tc_body (GRHSs _ grhss) res_ty = do
  grhss' <- tcGRHSList ctxt tc_body grhss res_ty
  return $ GRHSs emptyComments grhss'

tcGRHSList
  :: forall body. AnnoBody body
  => CsMatchContextRn
  -> TcMatchAltChecker body
  -> [LGRHS Rn (LocatedA (body Rn))]
  -> ExpRhoType
  -> TcM [LGRHS Tc (LocatedA (body Tc))]
tcGRHSList ctxt tc_body grhss res_ty = do
  (usages, grhss') <- mapAndUnzipM (wrapLocSndMA tc_alt) grhss
  tcEmitBindingUsage$ supUEs usages
  return grhss'
  where
    stmt_ctxt = PatGuard ctxt

    tc_alt :: GRHS Rn (LocatedA (body Rn)) -> TcM (UsageEnv, GRHS Tc (LocatedA (body Tc)))
    tc_alt (GRHS _ guards rhs) = tcCollectingUsage $ do
      (guards', rhs') <- tcStmtsAndThen stmt_ctxt tcGuardStmt guards res_ty
                         $ tc_body rhs
      return (GRHS noAnn guards' rhs')

{- *********************************************************************
*                                                                      *
            tcBody
*                                                                      *
********************************************************************* -}

tcBody :: LCsExpr Rn -> ExpRhoType -> TcM (LCsExpr Tc)
tcBody body res_ty = do
  traceTc "tcBody" (ppr res_ty)
  tcPolyLExpr body res_ty

{- *********************************************************************
*                                                                      *
            tcStmts
*                                                                      *
********************************************************************* -}

type TcExprStmtChecker = TcStmtChecker CsExpr ExpRhoType

type TcStmtChecker body rho_type
  = forall thing.
     CsStmtContextRn
  -> Stmt Rn (LocatedA (body Rn))
  -> rho_type
  -> (rho_type -> TcM thing)
  -> TcM (Stmt Tc (LocatedA (body Tc)), thing)

tcStmtsAndThen
  :: AnnoBody body
  => CsStmtContextRn
  -> TcStmtChecker body rho_type
  -> [LStmt Rn (LocatedA (body Rn))]
  -> rho_type
  -> (rho_type -> TcM thing)
  -> TcM ([LStmt Tc (LocatedA (body Tc))], thing)
tcStmtsAndThen _ _ [] res_ty thing_inside = do
  thing <- thing_inside res_ty
  return ([], thing)

tcStmtsAndThen ctxt stmt_chk (L loc (LetStmt x binds) : stmts) res_ty thing_inside = do
  (binds', _, (stmts', thing)) <- tcLocalBinds binds
                                  $ tcStmtsAndThen ctxt stmt_chk stmts res_ty thing_inside
  return (L loc (LetStmt x binds') : stmts', thing)

tcStmtsAndThen ctxt stmt_chk (L loc stmt : stmts) res_ty thing_inside = do
  (stmt', (stmts', thing)) <- setSrcSpanA loc
                              $ addErrCtxt (pprStmtInCtxt ctxt stmt)
                              $ stmt_chk ctxt stmt res_ty
                              $ \res_ty' -> popErrCtxt
                              $ tcStmtsAndThen ctxt stmt_chk stmts res_ty'
                              $ thing_inside
  return (L loc stmt' : stmts', thing)

---------------------------------------------------
--              Pattern guards
---------------------------------------------------

tcGuardStmt :: TcExprStmtChecker
tcGuardStmt _ (BodyStmt _ guard) res_ty thing_inside = do
  guard' <- tcScalingUsage Many $ tcCheckMonoExpr guard (asAnyTyKi boolTy)
  thing <- thing_inside res_ty
  return (BodyStmt (asAnyTyKi boolTy) guard', thing)

tcGuardStmt ctxt (BindStmt _ pat rhs) res_ty thing_inside = do
  (rhs', rhs_ty) <- tcScalingUsage Many $ tcInferRhoNC rhs
  (pat', thing) <- tcCheckPat_O (StmtCtxt ctxt) (lexprCtOrigin rhs) pat rhs_ty
                   $ thing_inside res_ty
  traceTc "tcGuardStmt"
    $ vcat [ ppr pat, ppr pat', ppr rhs, ppr rhs', ppr rhs_ty ]

  return (mkTcBindStmt pat' rhs', thing)

tcGuardStmt _ stmt _ _ = pprPanic "tcGuardStmt: unexpected Stmt" (ppr stmt)

{- *********************************************************************
*                                                                      *
            Errors and contexts
*                                                                      *
********************************************************************* -}

checkArgCounts
  :: AnnoBody body
  => MatchGroup Rn (LocatedA (body Rn))
  -> TcM VisArity
checkArgCounts (MG { mg_alts = L _ [] }) = panic "checkArgCounts/emptyMG"

checkArgCounts (MG { mg_alts = L _ (match1:matches) })
  | null matches
  = return n_args1
  | Just bad_matches <- mb_bad_matches
  = failWithTc $ TcRnMatchesHaveDiffNumArgs (m_ctxt (unLoc match1))
               $ MatchArgMatches match1 bad_matches
  | otherwise
  = return n_args1
  where
    n_args1 = reqd_args_in_match match1
    mb_bad_matches = NE.nonEmpty [m | m <- matches, reqd_args_in_match m /= n_args1]

    reqd_args_in_match (L _ (Match { m_pats = L _ pats })) = count (isVisArgPat . unLoc) pats
