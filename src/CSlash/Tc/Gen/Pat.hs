{-# LANGUAGE BangPatterns #-}
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
    $ do traceTc "tcMatchPats"
           $ vcat [ text "match_ctxt =" <+> ppr match_ctxt
                  , text "pats =" <+> ppr pats
                  , text "pat_tys =" <+> ppr pat_tys ]
         err_ctxt <- getErrCtxt
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
               -- we MUST have a binder of the form '/\ a' (parsed as a 'TyVarPat {}')
               | Required <- vis
               = do (_, res) <- tc_forall_lpat tv penv pat
                                $ loop pats pat_tys
                    return res

               -- we MAY have a binder of the form '/\ {a}' (parsed as a 'ImpPat _ (TyVarPat {})'
               | Specified <- vis
               , Just _ <- imp_lpat_maybe pat
               = do (_, res) <- tc_forall_lpat tv penv pat
                                $ loop pats pat_tys
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

tcPatBndr :: PatEnv -> Name -> ExpSigmaType -> TcM (AnyCsWrapper, TcId)
tcPatBndr penv@(PE { pe_ctxt = LetPat }) bndr_name exp_pat_ty = panic "tcPatBndr let"

tcPatBndr _ bndr_name pat_ty = do
  pat_ty <- expTypeToType pat_ty
  traceTc "tcPatBndr(not let)" (ppr bndr_name $$ ppr pat_ty)
  return (idCsWrapper, mkLocalIdOrTyCoVar bndr_name pat_ty)

newLetBndr :: Name -> AnyType -> TcM TcId
newLetBndr name ty = do
  mono_name <- cloneLocalName name
  return $ mkLocalId mono_name ty

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

  TyVarPat x (L l name) -> panic "tc_pat: TyVarPat"

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

  other -> pprPanic "tc_pat unfinished" (ppr other)

tc_forall_lpat :: AnyTyVar AnyKiVar -> Checker (LPat Rn) (LPat Tc)
tc_forall_lpat tv penv (L span pat) thing_inside = setSrcSpanA span $ do
  (pat', res) <- maybeWrapPatCtxt pat (tc_forall_pat tv penv pat) thing_inside
  return (L span pat', res)

tc_forall_pat :: AnyTyVar AnyKiVar -> Checker (Pat Rn) (Pat Tc)

tc_forall_pat tv penv (ParPat x lpat) thing_inside = do
  (lpat', res) <- tc_forall_lpat tv penv lpat thing_inside
  return (ParPat x lpat', res)

tc_forall_pat tv penv (ImpPat x lpat) thing_inside = do
  (lpat', res) <- tc_forall_lpat tv penv lpat thing_inside
  return (ImpPat x lpat', res)

tc_forall_pat tv _ pat thing_inside = do
  tp <- pat_to_type_pat pat
  (arg_ty, result) <- tc_ty_pat tp tv thing_inside
  let pat' = XPat $ TyPat pat arg_ty tp
  return (pat', result)

pat_to_type_pat :: Pat Rn -> TcM (CsTyPat Rn)
pat_to_type_pat pat = do
  (ty, x) <- runWriterT (pat_to_type pat)
  pure (CsTP (buildCsTyPatRn x) ty)

pat_to_type :: Pat Rn -> WriterT CsTyPatRnBuilder TcM (LCsType Rn)

pat_to_type (TyVarPat _ lname) = do
  tell (tpBuilderExplicitTV (unLoc lname))
  return b
  where b = noLocA (CsTyVar noAnn lname)

pat_to_type (WildPat _) = return b
  where b = noLocA (CsUnboundTyVar noExtField (panic "CsUnboundTyVar rdrname"))

pat_to_type (ImpPat _ pat) = pat_to_type (unLoc pat)

pat_to_type (ParPat _ pat) = do
  t <- pat_to_type (unLoc pat)
  return (noLocA (CsParTy noAnn t))

pat_to_type (KdSigPat _ pat sig_ki) = do
  t <- pat_to_type (unLoc pat)
  let !(CsPSK x_cspsk k) = sig_ki
      b = noLocA (CsKindSig noAnn t k)
  tell (tpBuilderPatSig x_cspsk)
  return b

pat_to_type pat = lift $ failWith $ panic "TcRnIllformedTypePattern pat"

tc_ty_pat :: CsTyPat Rn -> AnyTyVar AnyKiVar -> TcM r -> TcM (AnyType, r)
tc_ty_pat tp tv thing_inside = do
  (sig_ibs, sig_kibs, arg_ty) <- tcCsTyPat tp (varKind tv)
  _ <- unifyType Nothing arg_ty (mkTyVarTy tv)
  result <- tcExtendNameKiVarEnv sig_kibs
            $ tcExtendNameTyVarEnv sig_ibs
            $ thing_inside
  return (arg_ty, result)

{- *********************************************************************
*                                                                      *
            Pattern signatures   (pat :: type)
*                                                                      *
********************************************************************* -}

tcPatSig :: CsPatSigType Rn -> ExpSigmaType -> TcM (AnyType, AnyCsWrapper)
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
