{-# LANGUAGE LambdaCase #-}
module CSlash.CsToCore.Utils where

import CSlash.Cs
import CSlash.Core as Core
import CSlash.CsToCore.Monad

import CSlash.Core.Utils
import CSlash.Core.Make
import CSlash.Types.Var.Id.Make
import CSlash.Types.Var.Id
import CSlash.Types.Literal
import CSlash.Core.TyCon
import CSlash.Core.DataCon
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.Kind.Compare
import CSlash.Builtin.Types
import CSlash.Core.ConLike
import CSlash.Types.Unique.Set
import CSlash.Types.Unique.Supply
import CSlash.Unit.Module
import CSlash.Builtin.Names
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Types.SrcLoc
import CSlash.Types.Tickish
import CSlash.Utils.Misc
import CSlash.Driver.DynFlags
import CSlash.Driver.Ppr

import CSlash.Tc.Types.Evidence

import Control.Monad (zipWithM)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NEL
import Data.Maybe (maybeToList)

{-**********************************************************************
*                                                                      *
           Selecting match variables
*                                                                      *
**********************************************************************-}

selectMatchVars :: [Pat Zk] -> DsM [Id Zk]
selectMatchVars ps = mapM selectMatchVar ps

selectMatchVar :: Pat Zk -> DsM (Id Zk)
selectMatchVar (ParPat _ pat) = selectMatchVar (unLoc pat)
selectMatchVar (VarPat _ var) = return (localizeId (unLoc var))
selectMatchVar (AsPat _ var _) = assert (idKind (unLoc var) `eqKind` Mono (BIKi UKd)) $
                                 return (localizeId (unLoc var))
selectMatchVar (TyVarPat{}) = panic "selectMatchVar TyVarPat"
selectMatchVar (ImpPat{}) = panic "selectMatchVar ImpPat"
selectMatchVar pat = newSysLocalDs (panic "csPatType pat")

{-**********************************************************************
*                                                                      *
           EquationInfo 
*                                                                      *
**********************************************************************-}

firstPat :: EquationInfoNE -> Pat Zk
firstPat (EqnMatch {eqn_pat =pat}) = unLoc pat
firstPat  (EqnDone {}) = error "firstPat: no patterns"

shiftEqns :: Functor f => f EquationInfoNE -> f EquationInfo
shiftEqns = fmap shift
  where
    shift (EqnMatch { eqn_rest = rest }) = rest
    shift eqn@(EqnDone {}) = pprPanic "shiftEqns" (ppr eqn)

combineEqnRhss :: NonEmpty EquationInfo -> DsM (MatchResult CoreExpr)
combineEqnRhss eqns = return $ foldr1 combineMatchResults $ map eqnMatchResult (NEL.toList eqns)

cantFailMatchResult :: CoreExpr -> MatchResult CoreExpr
cantFailMatchResult expr = MR_Infallible $ return expr

extractMatchResult :: MatchResult CoreExpr -> CoreExpr -> DsM CoreExpr
extractMatchResult match_result failure_expr =
  runMatchResult failure_expr (shareFailureHandler match_result)

combineMatchResults :: MatchResult CoreExpr -> MatchResult CoreExpr -> MatchResult CoreExpr
combineMatchResults match_result1@(MR_Infallible _) _
  = match_result1
combineMatchResults match_result1 match_result2 =
  case shareFailureHandler match_result1 of
    MR_Infallible _ -> match_result1
    MR_Fallible body_fn1 -> MR_Fallible $ \fail_expr ->
      body_fn1 =<< runMatchResult fail_expr match_result2

adjustMatchResultDs :: (a -> DsM b) -> MatchResult a -> MatchResult b
adjustMatchResultDs encl_fn = \case
  MR_Infallible body_fn -> MR_Infallible $ encl_fn =<< body_fn
  MR_Fallible body_fn -> MR_Fallible $ \fail -> encl_fn =<< body_fn fail

wrapBind :: Id Zk -> Id Zk -> CoreExpr -> CoreExpr
wrapBind new old body
  | new == old = body
  | otherwise = Let (NonRec (Core.Id new) (varToCoreExpr old)) body

mkGuardedMatchResult :: CoreExpr -> MatchResult CoreExpr -> MatchResult CoreExpr
mkGuardedMatchResult pred_expr mr = MR_Fallible $ \fail -> do
  body <- runMatchResult fail mr
  return $ mkIfThenElse pred_expr body fail

{-**********************************************************************
*                                                                      *
           Desugarer's version of Core Functions
*                                                                      *
**********************************************************************-}

mkFailExpr :: CsMatchContextRn -> Type Zk -> DsM CoreExpr
mkFailExpr ctxt ty
  = return $ panic "mkFailExpr"

mkCastDs :: CoreExpr -> TypeCoercion Zk -> CoreExpr
mkCastDs e co | isReflTyCo co = e
              | otherwise = Cast e co

{-**********************************************************************
*                                                                      *
           Code for pattern-matching and other failures
*                                                                      *
**********************************************************************-}

mkFailurePair :: CoreExpr -> DsM (CoreBind, CoreExpr)
mkFailurePair expr = do
  fail_fun_var <- newFailLocalMDs (mkFunTy (BIKi UKd) (mkAppTy unitTy (Embed (BIKi UKd))) ty)
  fail_fun_arg <- newSysLocalMDs (mkAppTy unitTy (Embed (BIKi UKd)))
  let real_arg = setOneShotLambda fail_fun_arg
  return ( NonRec (Core.Id fail_fun_var) (Lam (Core.Id real_arg) (Just (BIKi UKd)) expr)
         , App (Var fail_fun_var) unitExpr )
  where ty = exprType expr

shareFailureHandler :: MatchResult CoreExpr -> MatchResult CoreExpr
shareFailureHandler mr@(MR_Infallible _) = mr
shareFailureHandler (MR_Fallible match_fn) = MR_Fallible $ \fail_expr -> do
  (fail_bind, shared_failure_handler) <- mkFailurePair fail_expr
  body <- match_fn shared_failure_handler
  return $ Let fail_bind body

{- *********************************************************************
*                                                                      *
              Ticks
*                                                                      *
********************************************************************* -}

mkOptTickBox :: [CoreTickish] -> CoreExpr -> CoreExpr
mkOptTickBox = flip (foldr Tick)

-- *********************************************************************

isTrueLCsExpr :: LCsExpr Zk -> Maybe (CoreExpr -> DsM CoreExpr)
-- isTrueLCsExpr (L _ (CsVar _ (L _ v)))
--   | v `hasKey` getUnique trueDataConId
-- isTrueLCsExpr
-- isTrueLCsExpr
isTrueLCsExpr = panic "isTrueLCsExpr"
