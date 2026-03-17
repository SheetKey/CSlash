module CSlash.CsToCore.GuardedRHSs where

import {-# SOURCE #-} CSlash.CsToCore.Expr  ( dsLExpr, dsLocalBinds )
import {-# SOURCE #-} CSlash.CsToCore.Match ( matchSinglePatVar )

import CSlash.Cs
import CSlash.Core.Make
import CSlash.Core
import CSlash.Core.Utils (bindNonRec)

import CSlash.CsToCore.Monad
import CSlash.CsToCore.Utils
import CSlash.CsToCore.Pmc.Types ( Nablas )
import CSlash.Core.Type ( Type )
import CSlash.Types.SrcLoc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Core.Kind
import Control.Monad ( zipWithM )
import Data.List.NonEmpty ( NonEmpty, toList )

dsGRHSs
  :: CsMatchContextRn
  -> GRHSs Zk (LCsExpr Zk)
  -> Type Zk
  -> NonEmpty Nablas
  -> DsM (MatchResult CoreExpr)
dsGRHSs cs_ctx (GRHSs _ grhss) rhs_ty rhss_nablas = do
  match_results <- assert (length grhss == length rhss_nablas)
                   $ zipWithM (dsGRHS cs_ctx rhs_ty) (toList rhss_nablas) grhss
  nablas <- getPmNablas
  return $ foldr1 combineMatchResults match_results

dsGRHS
  :: CsMatchContextRn
  -> Type Zk
  -> Nablas
  -> LGRHS Zk (LCsExpr Zk)
  -> DsM (MatchResult CoreExpr)
dsGRHS cs_ctx rhs_ty rhs_nablas (L _ (GRHS _ guards rhs))
  = updPmNablas rhs_nablas
    $ matchGuards (map unLoc guards) cs_ctx rhs rhs_ty

{- *********************************************************************
*                                                                      *
*  matchGuard : make a MatchResult CoreExpr CoreExpr from a guarded RHS                  
*                                                                      *
********************************************************************* -}

matchGuards
  :: [GuardStmt Zk]
  -> CsMatchContextRn
  -> LCsExpr Zk
  -> Type Zk
  -> DsM (MatchResult CoreExpr)
matchGuards [] _ rhs _ = do
  core_rhs <- dsLExpr rhs
  return (cantFailMatchResult core_rhs)
matchGuards (BodyStmt _ e : stmts) ctx rhs rhs_ty
  | Just addTicks <- isTrueLCsExpr e = do
      match_result <- matchGuards stmts ctx rhs rhs_ty
      return (adjustMatchResultDs addTicks match_result)
matchGuards (BodyStmt _ expr : stmts) ctx rhs rhs_ty = do
  match_result <- matchGuards stmts ctx rhs rhs_ty
  pred_expr <- dsLExpr expr
  return (mkGuardedMatchResult pred_expr match_result)
matchGuards (LetStmt _ binds : stmts) ctx rhs rhs_ty = do
  ldi_nablas <- getPmNablas
  match_result <- matchGuards stmts ctx rhs rhs_ty
  return (adjustMatchResultDs (updPmNablas ldi_nablas . dsLocalBinds binds) match_result)
matchGuards (BindStmt _ pat bind_rhs : stmts) ctx rhs rhs_ty = do
  let upat = unLoc pat
  match_var <- selectMatchVar upat
  match_result <- matchGuards stmts ctx rhs rhs_ty
  core_rhs <- dsLExpr bind_rhs
  match_result' <- matchSinglePatVar match_var (Just core_rhs) (StmtCtxt $ PatGuard ctx)
                   pat rhs_ty match_result
  return $ bindNonRec match_var core_rhs <$> match_result'
