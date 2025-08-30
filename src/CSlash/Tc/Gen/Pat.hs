{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RankNTypes #-}

module CSlash.Tc.Gen.Pat where

-- import {-# SOURCE #-}   GHC.Tc.Gen.Expr( tcSyntaxOp, tcSyntaxOpGen, tcInferRho )

import CSlash.Cs
-- import CSlash.Cs.Syn.Type
import CSlash.Rename.Utils
import CSlash.Tc.Errors.Types
-- import GHC.Tc.Gen.Sig( TcPragEnv, lookupPragEnv, addInlinePrags )
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.Instantiate
import CSlash.Types.Id
import CSlash.Types.Var
import CSlash.Types.Name
import CSlash.Types.Name.Reader
import CSlash.Core.Kind
import CSlash.Tc.Utils.Env
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Zonk.TcType
import CSlash.Core.Type.Ppr ( pprTyVars )
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Utils.Unify
import CSlash.Tc.Gen.CsType
import CSlash.Tc.Solver (solveKindCoercions)
import CSlash.Builtin.Types
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.BasicTypes
import CSlash.Core.TyCon
import CSlash.Core.Type
import CSlash.Core.DataCon
import CSlash.Core.ConLike
import CSlash.Core.UsageEnv
import CSlash.Builtin.Names
import CSlash.Types.Basic hiding (SuccessFlag(..))
import CSlash.Driver.DynFlags
import CSlash.Types.SrcLoc
import CSlash.Types.Var.Set
import CSlash.Utils.Misc
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic
import Control.Arrow  ( second )
import Control.Monad
import CSlash.Data.FastString
import qualified Data.List.NonEmpty as NE

import CSlash.Data.List.SetOps ( getNth )

import Data.List( partition )
import Control.Monad.Trans.Writer.CPS
import Control.Monad.Trans.Class

{- *********************************************************************
*                                                                      *
                External interface
*                                                                      *
********************************************************************* -}

tcMatchPats
  :: forall a.
     CsMatchContextRn
  -> [LPat Rn]
  -> [ExpPatType]
  -> TcM a
  -> TcM ([LPat Tc], a)
tcMatchPats match_ctxt pats pat_tys thing_inside
  = assertPpr (count isVisibleExpPatType pat_tys == count (isVisArgPat . unLoc) pats)
              (ppr pats $$ ppr pat_tys)
    $ do err_ctxt <- getErrCtxt
         let loop_init :: [LPat Rn] -> [ExpPatType] -> TcM ([LPat Tc], a)
             -- deal with ExpForAllPatKis which should only appear at the start
             loop_init all_pats (ExpForAllPatKi kv : pat_tys)
               = loop_init all_pats pat_tys

             loop_init all_pats pat_tys = loop all_pats pat_tys

             loop :: [LPat Rn] -> [ExpPatType] -> TcM ([LPat Tc], a)
             -- no more pats
             loop [] pat_tys
               = assertPpr (not (any isVisibleExpPatType pat_tys)) (ppr pats $$ ppr pat_tys)
                 $ do res <- setErrCtxt err_ctxt thing_inside
                      return ([], res)
             -- ExpForAllPatTy, wants a type pattern
             loop all_pats@(pat : pats) (ExpForAllPatTy (Bndr tv vis) : pat_tys)
               | Required <- vis
               , Just _ <- imp_lpat_maybe pat
               = pprPanic "tcMatchPats"
                 $ vcat [ text "Required ExpForAllPatTy but found implicit pattern"
                        , ppr tv <+> ppr vis
                        , ppr pat ]
               
               | Required <- vis
               = do (_, res) <- tc_ty_pat (unLoc pat) tv $ loop pats pat_tys
                    return res

               | Specified <- vis
               , Just (L _ imp_pat) <- imp_lpat_maybe pat
               = do (_, res) <- tc_ty_pat imp_pat tv $ loop pats pat_tys
                    return res

               | otherwise
               = loop all_pats pat_tys
             -- InvisPat with no corresponding ExpForAllPatTy
             loop (pat : _) _
               | Just imp_pat <- imp_lpat_maybe pat
               = panic "failAt (locA loc) (TcRnInvisPatWithNoForAll imp_pat)"
             -- ExpForAllPatKi
             loop all_pats (ExpForAllPatKi kv : pat_tys)
               = panic "tcMatchPats/ExpForAllPatKi"
             -- ExpFunPatTy
             loop (pat : pats) (ExpFunPatTy pat_ty : pat_tys)
               = do (p, (ps, res)) <- tc_lpat pat_ty penv pat $ loop pats pat_tys
                    return (p : ps, res)
             -- failure
             loop pats@(_:_) [] = pprPanic "tcMatchPats" (ppr pats)

         loop_init pats pat_tys
  where
    penv = PE { pe_ctxt = LamPat match_ctxt, pe_orig = PatOrigin }

    imp_lpat_maybe :: LPat Rn -> Maybe (LPat Rn)
    imp_lpat_maybe (L _ pat) = imp_pat_maybe pat

    imp_pat_maybe :: Pat Rn -> Maybe (LPat Rn)
    imp_pat_maybe (ParPat _ lpat) = imp_lpat_maybe lpat
    imp_pat_maybe (ImpPat _ lpat) = Just lpat
    imp_pat_maybe _ = Nothing

tcCheckPat_O
  :: CsMatchContextRn
  -> CtOrigin
  -> LPat Rn
  -> AnySigmaType
  -> TcM a
  -> TcM (LPat Tc, a)
tcCheckPat_O ctxt orig pat pat_ty thing_inside
  = tc_lpat (mkCheckExpType pat_ty) penv pat thing_inside
  where
    penv = PE { pe_ctxt = LamPat ctxt, pe_orig = orig }

{- *********************************************************************
*                                                                      *
                PatEnv, PatCtxt, LetBndrSpec
*                                                                      *
********************************************************************* -}

data PatEnv = PE
  { pe_ctxt :: PatCtxt
  , pe_orig :: CtOrigin
  }

data PatCtxt
  = LamPat CsMatchContextRn
  | LetPat

{- *********************************************************************
*                                                                      *
                Binders
*                                                                      *
********************************************************************* -}

tcPatBndr :: PatEnv -> Name -> ExpSigmaType -> TcM (CsWrapper, TcId)
tcPatBndr penv@(PE { pe_ctxt = LetPat }) bndr_name exp_pat_ty = panic "tcPatBndr let"

tcPatBndr _ bndr_name pat_ty = do
  pat_ty <- expTypeToType pat_ty
  traceTc "tcPatBndr(not let)" (ppr bndr_name $$ ppr pat_ty)
  return (idCsWrapper, mkLocalIdOrTyCoVar bndr_name pat_ty)

{- *********************************************************************
*                                                                      *
                The main worker functions
*                                                                      *
********************************************************************* -}

type Checker inp out
  = forall r. PatEnv -> inp -> TcM r -> TcM (out, r)

tc_lpat :: ExpSigmaType -> Checker (LPat Rn) (LPat Tc)
tc_lpat pat_ty penv (L span pat) thing_inside = setSrcSpanA span $ do
  (pat', res) <- maybeWrapPatCtxt pat (tc_pat pat_ty penv pat) thing_inside
  return (L span pat', res)

tc_pat :: ExpSigmaType -> Checker (Pat Rn) (Pat Tc)
tc_pat pat_ty penv ps_pat thing_inside = case ps_pat of
  VarPat x (L l name) -> do
    (wrap, id) <- tcPatBndr penv name pat_ty
    (res, mult_wrap) <- tcCheckUsage name (idKind id)
           $ tcExtendIdEnv1 name id thing_inside
    pat_ty <- readExpType pat_ty
    return (mkCsWrapPat (wrap <.> mult_wrap) (VarPat x (L l id)) pat_ty, res)

  ParPat x pat -> do
    (pat', res) <- tc_lpat pat_ty penv pat thing_inside
    return (ParPat x pat', res)

  WildPat _ -> do
    panic "checkManyPattern/but really we want affine constraint"

  AsPat x (L nm_loc name) pat -> do
    panic "AsPat"

  SigPat _ pat sig_ty -> do
    (inner_ty, wrap) <- tcPatSig sig_ty pat_ty
    (pat', res) <- tc_lpat (mkCheckExpType inner_ty) penv pat thing_inside
    pat_ty <- readExpType pat_ty
    return (mkCsWrapPat wrap (SigPat inner_ty pat' sig_ty) pat_ty, res)

  _ -> panic "tc_pat unfinished"

tc_ty_pat :: Pat Rn -> AnyTyVar AnyKiVar -> TcM r -> TcM (AnyType, r)
tc_ty_pat tp tv thing_inside = do
  let mb_kind = let go pat = case pat of
                               TyVarPat {} -> Nothing
                               WildPat {} -> Nothing
                               ParPat _ (L _ p) -> go p
                               KdSigPat _ _ (CsPSK _ k) -> Just k
                               _ -> pprPanic "tc_ty_pat" (ppr pat)
                in go tp
      expected_kind = varKind tv
  traceTc "tc_ty_pat 1" (ppr expected_kind)
  (name, is_wild) <- let go pat = case pat of
                                    TyVarPat _ (L _ n) -> return (n, False)
                                    WildPat _ -> (, True) <$> newSysName (mkTyVarOcc "_")
                                    ParPat _ (L _ p) -> go p
                                    KdSigPat _ (L _ p) _ -> go p
                                    _ -> pprPanic "tc_ty_pat" (ppr pat)
          in go tp
  let mb_name = if is_wild then Nothing else Just name

  pat_tv <- newPatTyVar name expected_kind
  let sig_bv = case mb_name of
                 Nothing -> []
                 Just nm -> [(nm, toAnyTyVar pat_tv)]

  arg_ty <- case mb_kind of
    Nothing -> return (mkTyVarTy (toAnyTyVar pat_tv))
    Just pat_ki -> do
      addKindCtxt pat_ki
        $ solveKindCoercions "tc_ty_pat"
        $ tcCsTvbKind mb_name pat_ki expected_kind

      traceTc "tc_ty_pat 2"
        $ vcat [ text "expected_kind" <+> ppr expected_kind
               , text "(name, pat_tv)" <+> ppr (name, pat_tv) ]

      return (mkTyVarTy (toAnyTyVar pat_tv))

  _ <- unifyType Nothing arg_ty (mkTyVarTy tv)
  result <- tcExtendNameTyVarEnv sig_bv $ thing_inside
  return (arg_ty, result)

{- *********************************************************************
*                                                                      *
            Pattern signatures   (pat :: type)
*                                                                      *
********************************************************************* -}

tcPatSig :: CsPatSigType Rn -> ExpSigmaType -> TcM (AnyType, CsWrapper)
tcPatSig sig res_ty = do
  sig_ty <- tcCsPatSigType PatSigCtxt sig AnyMonoKind

  wrap <- addErrCtxtM (mk_msg sig_ty)
          $ tcSubTypePat PatSigOrigin PatSigCtxt res_ty sig_ty
  return (sig_ty, wrap)
  where
    mk_msg sig_ty tidy_env = do
      (tidy_env, sig_ty) <- zonkTidyTcType tidy_env sig_ty
      res_ty <- readExpType res_ty
      (tidy_env, res_ty) <- zonkTidyTcType tidy_env res_ty
      let msg = vcat [ hang (text "When checking that the pattern signature:")
                       4 (ppr sig_ty)
                     , nest 2 (hang (text "fits the type of its context:")
                               2 (ppr res_ty)) ]
      return (tidy_env, msg)

{- *********************************************************************
*                                                                      *
            Errors and contexts
*                                                                      *
********************************************************************* -}

maybeWrapPatCtxt :: Pat Rn -> (TcM a -> TcM b) -> TcM a -> TcM b
maybeWrapPatCtxt pat tcm thing_inside
  | not (worth_wrapping pat) = tcm thing_inside
  | otherwise = addErrCtxt msg $ tcm $ popErrCtxt thing_inside
  where
    worth_wrapping VarPat {} = False
    worth_wrapping TyVarPat {} = False
    worth_wrapping ParPat {} = False
    worth_wrapping AsPat {} = False
    worth_wrapping _ = True
    msg = hang (text "In the pattern:") 2 (ppr pat)
