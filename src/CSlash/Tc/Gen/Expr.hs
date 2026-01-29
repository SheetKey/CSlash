module CSlash.Tc.Gen.Expr where

import CSlash.Cs
-- import CSlash.Cs.Syn.Type
import CSlash.Rename.Utils
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.Unify
import CSlash.Tc.Types.BasicTypes
import CSlash.Types.Basic
import CSlash.Types.Error
import CSlash.Types.Var
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Map
import CSlash.Types.Unique.Set
import CSlash.Core.Kind
import CSlash.Core.UsageEnv
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Instantiate
import CSlash.Tc.Gen.App
import CSlash.Tc.Gen.Head
import CSlash.Tc.Gen.Bind        ( tcLocalBinds )
import CSlash.Rename.Env         ( addUsedGRE )
import CSlash.Tc.Utils.Env
-- import CSlash.Tc.Gen.Arrow
import CSlash.Tc.Gen.Match ( tcBody, tcLambdaMatches{-, tcCaseMatches-}
                           , tcGRHSList )
import CSlash.Tc.Gen.CsType
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Zonk.TcType
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.TcType as TcType
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Core.ConLike
import CSlash.Core.DataCon
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Types.Name.Reader
import CSlash.Core.TyCon
import CSlash.Core.Type
import CSlash.Tc.Types.Evidence
import CSlash.Builtin.Types
import CSlash.Builtin.Names
-- import CSlash.Builtin.Uniques ( mkBuiltinUnique )
import CSlash.Driver.DynFlags
import CSlash.Types.SrcLoc
import CSlash.Utils.Misc
import CSlash.Data.List.SetOps
import CSlash.Data.Maybe
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic

import Control.Monad
import qualified Data.List.NonEmpty as NE


{- *********************************************************************
*                                                                      *
            Main wrappers
*                                                                      *
********************************************************************* -}

tcCheckPolyExpr :: LCsExpr Rn -> SigmaType Tc -> TcM (LCsExpr Tc)
tcCheckPolyExpr expr res_ty = tcPolyLExpr expr (mkCheckExpType res_ty)

tcPolyLExpr :: LCsExpr Rn -> ExpSigmaType -> TcM (LCsExpr Tc)
tcPolyLExpr (L loc expr) res_ty =
  setSrcSpanA loc
  $ addExprCtxt expr
  $ do expr' <- tcPolyExpr expr res_ty
       return (L loc expr')

tcPolyExpr :: CsExpr Rn -> ExpSigmaType -> TcM (CsExpr Tc) 
tcPolyExpr e (Infer inf) = tcExpr e (Infer inf)
tcPolyExpr e (Check ty) = tcPolyExprCheck e (Left ty)

tcPolyLExprSig :: LCsExpr Rn -> TcCompleteSig -> TcM (LCsExpr Tc)
tcPolyLExprSig (L loc expr) sig = setSrcSpanA loc $ do
  traceTc "tcPolyLExprSig" (ppr loc $$ ppr expr)
  expr' <- tcPolyExprCheck expr (Right sig)
  return (L loc expr')

tcPolyExprCheck :: CsExpr Rn -> Either (SigmaType Tc) TcCompleteSig -> TcM (CsExpr Tc)
tcPolyExprCheck  expr res_ty = outer_skolemize res_ty $ \pat_tys rho_ty ->
  let tc_body (CsPar x (L loc e))
        = setSrcSpanA loc $ do e' <- tc_body e
                               return (CsPar x (L loc e'))

      tc_body e@(CsLam x matches) = do
        (wrap, matches') <- tcLambdaMatches e matches pat_tys (mkCheckExpType rho_ty)
        return (mkCsWrap wrap $ CsLam x matches')

      tc_body e = tcExpr e (mkCheckExpType rho_ty)
  in tc_body expr
  where
    outer_skolemize
      :: Either (SigmaType Tc) TcCompleteSig
      -> ([ExpPatType] -> RhoType Tc -> TcM (CsExpr Tc))
      -> TcM (CsExpr Tc)
    outer_skolemize (Left ty) thing_inside = do
      (wrap, expr') <- tcSkolemizeExpectedType ty thing_inside
      return (mkCsWrap wrap expr')
    outer_skolemize (Right sig) thing_inside = do
      (wrap, expr') <- tcSkolemizeCompleteSig sig thing_inside
      return ( mkCsWrap wrap expr')
        
{- *********************************************************************
*                                                                      *
        tcExpr: the main expression typechecker
*                                                                      *
********************************************************************* -}

tcInferRhoNC :: LCsExpr Rn -> TcM (LCsExpr Tc, RhoType Tc)
tcInferRhoNC = panic "tcInferRhoNC"

tcCheckMonoExpr :: LCsExpr Rn -> RhoType Tc -> TcM (LCsExpr Tc)
tcCheckMonoExpr expr res_ty = tcMonoExpr expr (mkCheckExpType res_ty)

tcMonoExpr :: LCsExpr Rn -> ExpRhoType -> TcM (LCsExpr Tc)
tcMonoExpr (L loc expr) res_ty
  = setSrcSpanA loc
    $ addExprCtxt expr
    $ do expr' <- tcExpr expr res_ty
         return (L loc expr')

tcExpr :: CsExpr Rn -> ExpRhoType -> TcM (CsExpr Tc)
-- Onto QuickLook
tcExpr e@(CsVar {}) res_ty = tcApp e res_ty
tcExpr e@(CsApp {}) res_ty = tcApp e res_ty
tcExpr e@(OpApp {}) res_ty = tcApp e res_ty
tcExpr e@(ExprWithTySig {}) res_ty = tcApp e res_ty
-- rest
tcExpr e@(CsOverLit _ lit) res_ty = panic "tcExpr CsOverLit"

tcExpr e@(CsLit x lit) res_ty = panic "tcExpr CsLit"

tcExpr (CsUnboundVar _ occ) res_ty = pprPanic "tcExpr CsUnboundVar" (ppr occ $$ ppr res_ty)

tcExpr (CsPar x expr) res_ty = panic "tcExpr CsPar"

tcExpr (NegApp x expr neg_expr) res_ty = panic "tcExpr NegApp"

tcExpr e@(CsLam x matches) res_ty = do
  (wrap, matches') <- tcLambdaMatches e matches [] res_ty
  return $ mkCsWrap wrap $ CsLam x matches'

tcExpr e@(CsTyLam x matches) res_ty = do
 -- Either: 1. generate some patterns here to pass instead of the empty list
  -- 2. in tcMatchPats we need to check for 'TyVarPat' or 'InvisPat' when the pattern is 'ExpFunPatTy Infer {..}'
  -- 3. Error on this (in line with what GHC does right now: only allows ty pats in lambdas when there is a full sig to be pushed down)
  -- 2 seems more appealing: we just will the infered type with an 'Embed monoKi'
  -- 1,2 problems: what to do about the kind variables we have to introduce?? There's nothing to skolemize.
  -- 3 makes sense: Its silly to write '(/\a -> M) T'. Writing 'M' alone is the same. So, the only reason to support this is uniformity, not a compelling reason
  --        Even sillier: '(/\{a} -> M)'. The 'a' is inferred! so no reason to write this.
  -- Punch-line: If you write '(/\a -> blah) T args', whatever 'T' is was already in scope, so however T is used in the body can just be inferred or explicit.
  -- TODO: Check what error GHC throws for bad at pattern and where it is caught
  panic "tcExpr CsTyLam: not allowed in this place"

tcExpr expr@(ExplicitTuple x tup_args) res_ty
  | all tupArgPresent tup_args
  = do let arity = length tup_args
           tup_tc = tupleTyCon arity
       res_ty <- expTypeToType res_ty
       (coi, arg_tys) <- matchExpectedTyConApp tup_tc res_ty
       tup_args1 <- tcCheckExplicitTuple tup_args (drop ((arity * 2) + 1) arg_tys)
       return $ mkCsWrapTyCo coi (ExplicitTuple x tup_args1)
  | otherwise
  = panic "tcExpr ExplicitTuple section"

tcExpr (CsLet x binds expr) res_ty = do
  (binds', wrapper, expr') <- tcLocalBinds binds $
                              tcMonoExpr expr res_ty
  return (CsLet x binds' (mkLCsWrap wrapper expr'))

tcExpr (CsIf x pred b1 b2) res_ty = do
  pred' <- tcCheckMonoExpr pred $ mkAppTy boolTy (Embed $ BIKi UKd)
  (u1, b1') <- tcCollectingUsage $ tcMonoExpr b1 res_ty
  (u2, b2') <- tcCollectingUsage $ tcMonoExpr b1 res_ty
  tcEmitBindingUsage (supUE u1 u2)
  return (CsIf x pred' b1' b2')

tcExpr (CsMultiIf _ alts) res_ty = do
  alts' <- tcGRHSList MultiIfAlt tcBody alts res_ty
  res_ty <- readExpType res_ty
  return (CsMultiIf res_ty alts')

tcExpr e res_ty = panic "tcExpr other"

tcCheckExplicitTuple
  :: [CsTupArg Rn]
  -> [SigmaType Tc]
  -> TcM [CsTupArg Tc]
tcCheckExplicitTuple args tys = do
  massertPpr (equalLength args tys) (ppr tys)
  checkTupSize (length args)
  zipWith3M go [1,2..] args tys
  where
    go :: Int -> CsTupArg Rn -> Type Tc -> TcM (CsTupArg Tc)
    go  i (Missing {}) arg_ty = pprPanic "tcCheckExplicitTuple: tuple sections not handled here"
                                (ppr i $$ ppr arg_ty)
    go i (Present x expr) arg_ty = do
      expr' <- tcCheckPolyExpr expr arg_ty
      return $ Present x expr'
