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
import CSlash.Builtin.Types
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types.Origin
import CSlash.Core.TyCon
import CSlash.Core.Type
import CSlash.Core.DataCon
import CSlash.Core.ConLike
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
tcMatchPats = panic "tcMatchPats"

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
  -- VarPat x (L l name) -> do
  --   (wrap, id) <- tcPatBndr penv name pat_ty
  --   (res, mult_wrap) <- tcCheckUsage name pat_ty $ tcExtendIdEnv1 name id thing_inside
  _ -> panic "tc_pat"

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
