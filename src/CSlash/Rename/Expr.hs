{-# LANGUAGE ConstraintKinds #-}

module CSlash.Rename.Expr where

import CSlash.Data.FastString

import CSlash.Rename.Bind ( rnLocalBindsAndThen, rnLocalValBindsLHS, rnLocalValBindsRHS
                          , rnMatchGroup, rnGRHS, makeMiniFixityEnv)
import CSlash.Cs
import CSlash.Tc.Errors.Types
-- import GHC.Tc.Utils.Env ( isBrackStage )
import CSlash.Tc.Utils.Monad
import CSlash.Unit.Module ( getModule )
import CSlash.Rename.Env
import CSlash.Rename.Fixity
import CSlash.Rename.Utils
  ( bindLocalNamesFV, checkDupNames
  , bindLocalNames
  {-, mapMaybeFvRn-}, mapFvRn
  , warnUnusedLocalBinds{-, typeAppErr-}
  , wrapGenSpan{-, genCsIntegralLit, genCsTyLit
  , genCsVar, genLCsVar, genCsApp-}, genCsApps{-, genCsApps'
  , genAppType, isIrrefutableCsPat-} )
import CSlash.Rename.Unbound ( reportUnboundName )
import CSlash.Rename.CsType
import CSlash.Rename.Pat
import CSlash.Driver.DynFlags
import CSlash.Builtin.Names
-- import CSlash.Builtin.Types ( nilDataConName )

import CSlash.Types.Basic (TypeOrKind (TypeLevel))
import CSlash.Types.Fixity
import CSlash.Types.Id.Make
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Name.Reader
import CSlash.Types.Unique.Set
import CSlash.Types.SourceText
import CSlash.Types.SrcLoc
import CSlash.Utils.Misc
import CSlash.Data.List.SetOps ( removeDupsOn )
import CSlash.Data.Maybe
import CSlash.Utils.Error
import CSlash.Utils.Panic
import CSlash.Utils.Outputable as Outputable

import Control.Monad
import Data.List (unzip4, minimumBy)
import Data.List.NonEmpty ( NonEmpty(..), nonEmpty )
import Control.Arrow (first)
import Data.Ord
import Data.Array
import qualified Data.List.NonEmpty as NE

{- *********************************************************************
*                                                                      *
              Expressions
*                                                                      *
********************************************************************* -}

rnLExpr :: LCsExpr Ps -> RnM (LCsExpr Rn, FreeVars)
rnLExpr = wrapLocFstMA rnExpr

rnExpr :: CsExpr Ps -> RnM (CsExpr Rn, FreeVars)
rnExpr (CsVar _ (L l v)) = do
  mb_gre <- lookupExprOccRn v
  case mb_gre of
    Nothing -> rnUnboundVar v
    Just gre -> return (CsVar noExtField (L (l2l l) (greName gre)), unitFV (greName gre))

rnExpr (CsUnboundVar _ v) = return (CsUnboundVar noExtField v, emptyFVs)

rnExpr (CsOverLit x lit) = do
  ((lit', mb_neg), fvs) <- rnOverLit lit
  case mb_neg of
    Nothing -> return (CsOverLit x lit', fvs)
    Just neg -> return (CsApp noExtField (noLocA neg) (noLocA (CsOverLit x lit')), fvs)

rnExpr (CsLit x lit) = do
  rnLit lit
  return (CsLit x (convertLit lit), emptyFVs)

rnExpr (CsLam x matches) = do
  (matches', fvs_ms) <- rnMatchGroup LamAlt rnLExpr matches
  return (CsLam x matches', fvs_ms)

rnExpr (CsApp x fun arg) = do
  (fun', fvFun) <- rnLExpr fun
  (arg', fvArg) <- rnLExpr arg
  return (CsApp x fun' arg', fvFun `plusFV` fvArg)

rnExpr (CsTyLam x matches) = do
  (matches', fvs_ms) <- rnMatchGroup TyLamAlt rnLExpr matches
  return (CsTyLam x matches', fvs_ms)

rnExpr (CsTyApp {}) = panic "rnExpr CsTyApp"

rnExpr (OpApp _ e1 op e2) = do
  (e1', fv_e1) <- rnLExpr e1
  (e2', fv_e2) <- rnLExpr e2
  (op', fv_op) <- rnLExpr op

  fixity <- case op' of
              L _ (CsVar _ (L _ n)) -> lookupFixityRn n
              _ -> return (Fixity minPrecedence InfixL)

  final_e <- mkOpAppRn e1' op' fixity e2'
  return (final_e, fv_e1 `plusFV` fv_op `plusFV` fv_e2)

rnExpr (NegApp _ e _) = do
  (e', fv_e) <- rnLExpr e
  (neg_name, fv_neg) <- lookupSyntax negateName
  final_e <- mkNegAppRn e' neg_name
  return (final_e, fv_e `plusFV` fv_neg)

---------------------------------------------
-- Sections
rnExpr (CsPar _ (L loc (section@(SectionL {})))) = do
  (section', fvs) <- rnSection section
  return (CsPar noExtField (L loc section'), fvs)

rnExpr (CsPar _ (L loc (section@(SectionR {})))) = do
  (section', fvs) <- rnSection section
  return (CsPar noExtField (L loc section'), fvs)

rnExpr (CsPar _ e) = do
  (e', fvs) <- rnLExpr e
  return (CsPar noExtField e', fvs)

rnExpr expr@(SectionL {}) = do
  addErr (sectionErr expr)
  rnSection expr

rnExpr expr@(SectionR {}) = do
  addErr (sectionErr expr)
  rnSection expr
---------------------------------------------

rnExpr (ExplicitTuple _ tup_args) = do
  (tup_args', fvs) <- mapFvRn rnTupArg tup_args
  return (ExplicitTuple noExtField tup_args', fvs)
  where
    rnTupArg (Present x e) = do
      (e', fvs) <- rnLExpr e
      return (Present x e', fvs)
    rnTupArg (Missing _) = return (Missing noExtField, emptyFVs)

rnExpr (ExplicitSum _ alt arity expr) = do
  (expr', fvs) <- rnLExpr expr
  return (ExplicitSum noExtField alt arity expr', fvs)

rnExpr (CsCase _ expr matches) = do
  (expr', e_fvs) <- rnLExpr expr
  (matches', ms_fvs) <- rnMatchGroup CaseAlt rnLExpr matches
  return (CsCase CaseAlt expr' matches', e_fvs `plusFV` ms_fvs)

rnExpr (CsIf _ p b1 b2) = rnCsIf p b1 b2

rnExpr (CsMultiIf _ alts) = do
  (alts', fvs) <- mapFvRn (rnGRHS MultiIfAlt rnLExpr) alts
  return (CsMultiIf noExtField alts', fvs)

rnExpr (CsLet _ binds expr) = rnLocalBindsAndThen binds $ \binds' _ -> do
  (expr', fvExpr) <- rnLExpr expr
  return (CsLet noExtField binds' expr', fvExpr)

rnExpr (ExprWithTySig _ expr ty) = do
  (ty', fvTy) <- rnCsSigType ExprWithTySigCtx ty
  (expr', fvExpr) <- rnLExpr expr
  return (ExprWithTySig noExtField expr' ty', fvExpr `plusFV` fvTy)

rnExpr (CsEmbTy _ ty) = do
  (ty', fvs) <- rnLCsType CsTypeCtx ty
  return (CsEmbTy noExtField ty', fvs)

rnUnboundVar :: RdrName -> RnM (CsExpr Rn, FreeVars)
rnUnboundVar v = do
  deferOutOfScopeVariables <- goptM Opt_DeferOutOfScopeVariables
  unless (isUnqual v || deferOutOfScopeVariables) (reportUnboundName v >> return ())
  return (CsUnboundVar noExtField v, emptyFVs)

{- *********************************************************************
*                                                                      *
        Operator sections
*                                                                      *
********************************************************************* -}

rnSection :: CsExpr Ps -> RnM (CsExpr Rn, FreeVars)
rnSection section@(SectionR x op expr) = do
  (op', fvs_op) <- rnLExpr op
  (expr', fvs_expr) <- rnLExpr expr
  checkSectionPrec InfixR section op' expr'
  let ds_section = genCsApps rightSectionName [op', expr']
  return (ds_section, fvs_op `plusFV` fvs_expr)
  
rnSection section@(SectionL x expr op) = do
  (expr', fvs_expr) <- rnLExpr expr
  (op', fvs_op) <- rnLExpr op
  checkSectionPrec InfixL section op' expr'
  let ds_section = genCsApps leftSectionName [wrapGenSpan $ CsApp noExtField op' expr']
  return (ds_section, fvs_op `plusFV` fvs_expr)
  
rnSection other = pprPanic "rnSection" (ppr other)

{- *********************************************************************
*                                                                      *
              Stmts
*                                                                      *
********************************************************************* -}

type RnStmtsAnnoBody body
  = ( Outputable (body Ps) )

rnStmts
  :: RnStmtsAnnoBody body
  => CsStmtContextRn
  -> (body Ps -> RnM (body Rn, FreeVars))
  -> [LStmt Ps (LocatedA (body Ps))]
  -> ([Name] -> RnM (thing, FreeVars))
  -> RnM (([LStmt Rn (LocatedA (body Rn))], thing), FreeVars)
rnStmts ctxt rnBody stmts thing_inside = do
  ((stmts', thing), fvs) <- rnStmtsWithFreeVars ctxt rnBody stmts thing_inside
  return ((map fst stmts', thing), fvs)

rnStmtsWithFreeVars
  :: RnStmtsAnnoBody body
  => CsStmtContextRn
  -> ((body Ps) -> RnM ((body Rn), FreeVars))
  -> [LStmt Ps (LocatedA (body Ps))]
  -> ([Name] -> RnM (thing, FreeVars))
  -> RnM (([(LStmt Rn (LocatedA (body Rn)), FreeVars)], thing), FreeVars)
rnStmtsWithFreeVars ctxt _ [] thing_inside = do
  checkEmptyStmts ctxt
  (thing, fvs) <- thing_inside []
  return (([], thing), fvs)
rnStmtsWithFreeVars ctxt rnBody (lstmt@(L loc _) : lstmts) thing_inside
  | null lstmts
  = setSrcSpanA loc $ do
      lstmt' <- checkLastStmt ctxt lstmt
      rnStmt ctxt rnBody lstmt' thing_inside
  | otherwise
  = do ((stmts1, (stmts2, thing)), fvs) <- setSrcSpanA loc $ do
         checkStmt ctxt lstmt
         rnStmt ctxt rnBody lstmt $ \bndrs1 ->
           rnStmtsWithFreeVars ctxt rnBody lstmts $ \bndrs2 ->
             thing_inside (bndrs1 ++ bndrs2)
       return (((stmts1 ++ stmts2), thing), fvs)

rnStmt
  :: RnStmtsAnnoBody body
  => CsStmtContextRn
  -> (body Ps -> RnM (body Rn, FreeVars))
  -> LStmt Ps (LocatedA (body Ps))
  -> ([Name] -> RnM (thing, FreeVars))
  -> RnM (([(LStmt Rn (LocatedA (body Rn)), FreeVars)], thing), FreeVars)
rnStmt ctxt rnBody (L loc (BodyStmt _ (L lb body))) thing_inside = do
  (body', fv_expr) <- rnBody body
  (thing, fvs3) <- thing_inside []
  return ( ( [(L loc (BodyStmt noExtField (L lb body')), fv_expr)]
           , thing )
         , fv_expr `plusFV` fvs3 )

rnStmt ctxt rnBody (L loc (BindStmt _ pat (L lb body))) thing_inside = do
  (body', fv_expr) <- rnBody body
  rnPat (StmtCtxt ctxt) pat $ \pat' -> do
    (thing, fvs3) <- thing_inside (collectPatBinders CollNoDictBinders pat')
    return ( ( [(L loc (BindStmt noExtField pat' (L lb body')), fv_expr)]
             , thing )
           , fv_expr `plusFV` fvs3 )

rnStmt _ _ (L loc (LetStmt _ binds)) thing_inside
  = rnLocalBindsAndThen binds $ \binds' binds_fvs -> do
      (thing, fvs) <- thing_inside (collectLocalBinders CollNoDictBinders binds')
      return ( ( [(L loc (LetStmt noAnn binds'), binds_fvs)]
               , thing )
             , fvs )

{- *********************************************************************
*                                                                      *
      Errors
*                                                                      *
********************************************************************* -}

checkEmptyStmts :: CsStmtContextRn -> RnM ()
checkEmptyStmts ctxt = mapM_ (panic "addErr . TcRnEmptyStmtsGroup") mb_err
  where
    mb_err = case ctxt of
      PatGuard {} -> Nothing

checkLastStmt
  :: RnStmtsAnnoBody body
  => CsStmtContextRn
  -> LStmt Ps (LocatedA (body Ps))
  -> RnM (LStmt Ps (LocatedA (body Ps)))
checkLastStmt ctxt lstmt@(L loc stmt) = case ctxt of
  _ -> check_other
  where
    check_other = do
      checkStmt ctxt lstmt
      return lstmt

checkStmt
  :: RnStmtsAnnoBody body
  => CsStmtContextRn
  -> LStmt Ps (LocatedA (body Ps))
  -> RnM ()
checkStmt ctxt (L _ stmt) = do
  dflags <- getDynFlags
  case okStmt dflags ctxt stmt of
    True -> return ()
    False -> panic "addErr $ TcRnUnexpectedStatementInContext ctxt (UnexpectedStatement stmt)"

okStmt :: DynFlags -> CsStmtContextRn -> Stmt Ps (LocatedA (body Ps)) -> Bool
okStmt dflags ctxt stmt = case ctxt of
  PatGuard {} -> okPatGuardStmt stmt

okPatGuardStmt :: Stmt Ps (LocatedA (body Ps)) -> Bool
okPatGuardStmt stmt = case stmt of
  BodyStmt {} -> True
  BindStmt {} -> True
  LetStmt {} -> True
  _ -> False

sectionErr :: CsExpr Ps -> TcRnMessage
sectionErr _ = panic "TcRnSectionWithoutParentheses"

{- *********************************************************************
*                                                                      *
        Generating code for expanded things
*                                                                      *
********************************************************************* -}

rnCsIf :: LCsExpr Ps -> LCsExpr Ps -> LCsExpr Ps -> RnM (CsExpr Rn, FreeVars)
rnCsIf p b1 b2 = do
  (p', fvP) <- rnLExpr p
  (b1', fvB1) <- rnLExpr b1
  (b2', fvB2) <- rnLExpr b2
  let fvs_if = plusFVs [fvP, fvB1, fvB2]
      rn_if = CsIf noExtField p' b1' b2'
  return (rn_if, fvs_if)
