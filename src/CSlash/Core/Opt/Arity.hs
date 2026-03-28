module CSlash.Core.Opt.Arity where

import CSlash.Cs.Pass

import CSlash.Core as Core
import CSlash.Core.Make
-- import CSlash.Core.FVs
import CSlash.Core.Utils
import CSlash.Core.DataCon
import CSlash.Core.TyCon     ( TyCon, tyConArity, isInjectiveTyCon )
-- import CSlash.Core.TyCon.RecWalk     ( initRecTc, checkRecTc )

import CSlash.Core.Subst
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.Type.Compare( eqType )

import CSlash.Types.Demand
-- import CSlash.Types.Cpr( CprSig, mkCprSig, botCpr )
import CSlash.Types.Var.Id
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Basic
import CSlash.Types.Tickish

import CSlash.Builtin.Types.Prim
import CSlash.Builtin.Uniques

import CSlash.Data.FastString
import CSlash.Data.Graph.UnVar
import CSlash.Data.Pair

import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc

import Data.List.NonEmpty ( nonEmpty )
import qualified Data.List.NonEmpty as NE
import Data.Maybe( isJust )

joinRhsArity :: CoreExpr -> JoinArity
joinRhsArity (Lam _ _ e) = 1 + joinRhsArity e
joinRhsArity _ = 0

{- *********************************************************************
*                                                                      *
              typeArity
*                                                                      *
********************************************************************* -}

isOneShotBndr :: CoreBndr -> Bool
isOneShotBndr Tv{} = True
isOneShotBndr KCv{} = True -- TODO: double check
isOneShotBndr Kv{} = True
isOneShotBndr (Core.Id id) = idOneShotInfo id == OneShotLam

{- *********************************************************************
*                                                                      *
              The main eta-expander
*                                                                      *
********************************************************************* -}

etaExpand :: Arity -> CoreExpr -> CoreExpr
etaExpand n orig_expr = panic "exa_expand in_scope (replicate n NoOneShotInfo) orig_expr"
  -- where
  --   in_scope = {-# SCC "eta_expand:in-scopeX" #-}
  --              panic "mkTermInScopeSets (exprFreeVars orig_expr)"

{- *********************************************************************
*                                                                      *
                Eta reduction
*                                                                      *
********************************************************************* -}

tryEtaReduce
  :: UnVarSet
  -> [(CoreBndr, Maybe CoreMonoKind)]
  -> CoreExpr
  -> SubDemand
  -> Maybe CoreExpr
tryEtaReduce rec_ids bndrs body eval_sd
  = go (reverse bndrs) body (mkReflTyCo (exprType body))
  where
    incoming_arity = count (isRuntimeVar . fst) bndrs

    go :: [(CoreBndr, Maybe CoreMonoKind)] -> CoreExpr -> TypeCoercion Zk -> Maybe CoreExpr
    go bs (Cast e co1) co2 = go bs e (co1 `mkTyTransCo` co2)
    go bs (Tick t e) co
      | tickishFloatable t
      = (Tick t) <$> go bs e co
    go (b : bs) (App fun arg) co
      | Just (co', ticks) <- ok_arg b arg co (exprType fun)
      = (flip (foldr mkTick) ticks) <$> go bs fun co'
    go remaining_bndrs fun co
      | all (not. isRuntimeVar . fst) remaining_bndrs
      , remaining_bndrs `ltLength` bndrs
      , ok_fun fun
      , let used_vars = panic "case (exprFreeVars fun, varsOfTyCo co) of"
              -- ((ids1, tcvs1, tvs1, kcvs1, kvs1), (tcvs2, tvs2, kcvs2 kvs2))
              --   -> ( ids1
              --      , tcvs1 `unionVarSet` tcvs2
              --      , tvs1 `unionVarSet` tvs2
              --      , kcvs1 `unionVarSet` kcvs2
              --      , kvs1 `unionVarSet` kvs2 )
            reduced_bndrs = mkCoreBndrVarSets (fst <$> dropList remaining_bndrs bndrs)
      , used_vars `disjointCoreVarSets` reduced_bndrs
      = Just (mkCoreLams (reverse remaining_bndrs) (mkCast fun co))
    go _ _ _ = Nothing

    ok_fun (App fun (Type {})) = ok_fun fun
    ok_fun (App fun (KiCo {})) = ok_fun fun
    ok_fun (App fun (Kind {})) = ok_fun fun
    ok_fun (Cast fun _) = ok_fun fun
    ok_fun (Tick _ expr) = ok_fun expr
    ok_fun (Var fun_id) = is_eta_reduction_sound fun_id
    ok_fun _ = False

    is_eta_reduction_sound fun
      | fun `elemUnVarSet` rec_ids
      = False
      | cantEtaReduceFun fun
      = False
      | otherwise
      = fun_arity fun >= incoming_arity
        || all_calls_with_arity incoming_arity
        || all ok_lam bndrs

    all_calls_with_arity n = fstOf3 (peelManyCalls n eval_sd)

    fun_arity fun
      | arity > 0 = arity
      | isEvaldUnfolding (idUnfolding fun) = 1
      | otherwise = 0
      where
        arity = idArity fun

    ok_lam = not . isRuntimeVar . fst

    ok_arg
      :: (CoreBndr, Maybe CoreMonoKind)
      -> CoreExpr
      -> TypeCoercion Zk
      -> CoreType 
      -> Maybe (TypeCoercion Zk, [CoreTickish])
    ok_arg (Tv bndr, _) (Type arg_ty) co fun_ty
      | Just tv <- getTyVar_maybe arg_ty
      , bndr == tv = case splitForAllForAllTyBinder_maybe fun_ty of
          Just (Bndr _ vis, _) -> panic "TODO: deal with vis coercions"
          Nothing -> pprPanic "tryEtaReduce: type arg to non-forall type"
                     (text "fun:" <+> ppr bndr
                      $$ text "arg:" <+> ppr arg_ty
                      $$ text "fun_ty:" <+> ppr fun_ty)
    ok_arg (KCv bndr, _) (KiCo arg_co) co fun_ty = panic "unfinished"
    ok_arg (Kv bndr, _) (Kind arg_ki) co fun_ty = panic "unfinished"
    ok_arg (Core.Id bndr, _) (Var v) co fun_ty
      | bndr == v
      , Just (_, fki, _) <- splitFunTy_maybe fun_ty
      = Just (mkTyFunCo (mkReflKiCo fki) (mkReflTyCo (varType bndr)) co, [])
    ok_arg bndr (Cast e co_arg) co fun_ty = panic "unfinished"
    ok_arg bndr (Tick t arg) co fun_ty = panic "unfinished"
    ok_arg _ _ _ _ = Nothing

cantEtaReduceFun :: CoreId -> Bool
cantEtaReduceFun fun
  = hasNoBinding fun
    || isJoinId fun
    -- TODO: check if there is an issue since all my stuff is CBV!
    -- GHC does NOT eta reduce CBV workers

{- *********************************************************************
*                                                                      *
                The "push rules"
*                                                                      *
********************************************************************* -}

pushCoArgs :: TypeCoercion Zk -> [CoreArg] -> Maybe ([CoreArg], MTypeCoercion Zk)
pushCoArgs co [] = return ([], MCo co)
pushCoArgs co (arg:args) = do panic "pushCoArgs"
  -- (arg', m_co1) <- pushCoArg co arg
  -- case m_co1 of
  --   MCo co1 -> do (args', m_co2) <- pushCoArgs co1 args
  --                 return (arg':args', m_co2)
  --   MRefl -> return (arg':args, MRefl)

-- pushCoArg :: TypeCoercion Zk -> CoreArg -> Maybe (CoreArg, MTypeCoercion Zk)
-- pushCoArg co arg
--   | Type ty <- arg
--   = do (ty', m_co') <- pushCoTyArg co ty
--        return (Type ty', m_co')
--   | Kind ki <- arg
--   = do (ki', m_co') <- pushCoKiArg co ki
--        return (Kind ki', m_co')
--   | otherwise
--   = do (arg_mco, m_co') <- pushCoValArg co
--        let arg_mco' = checkReflexiveMCo arg_mco
--        return (arg `mkCastMCo` arg_mco', m_co')


pushCoDataCon
  :: DataCon Zk
  -> [CoreExpr]
  -> MTypeCoercion Zk
  -> Maybe (DataCon Zk, [CoreType], [CoreExpr])
pushCoDataCon = panic "pushCoDataCon"
