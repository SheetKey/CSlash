module CSlash.Core.Rules where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Unit.Module   ( Module )
import CSlash.Unit.Module.Env
import CSlash.Unit.Module.ModGuts( ModGuts(..) )
import CSlash.Unit.Module.Deps( Dependencies(..) )

import CSlash.Driver.DynFlags( DynFlags )
import CSlash.Driver.Ppr( showSDoc )

import CSlash.Core
import CSlash.Core.Subst
-- import CSlash.Core.SimpleOpt ( exprIsLambda_maybe )
import CSlash.Core.FVs
import CSlash.Core.Utils
import CSlash.Core.Ppr
-- import GHC.Core.Unify as Unify ( ruleMatchTyKiX )
import CSlash.Core.Type as Type
  ( Type, MTypeCoercion, getTyVar_maybe, tcSplitTyConApp_maybe )
import CSlash.Core.Type.Ppr( pprParendType )
-- import CSlash.Core.Tidy     ( tidyRules )
-- import GHC.Core.Map.Expr ( eqCoreExpr )
import CSlash.Core.Opt.Arity( etaExpandToJoinPointRule )
import CSlash.Core.Make ( mkCoreLams )
import CSlash.Core.Opt.OccurAnal( occurAnalyzeExpr )

-- import CSlash.Builtin.Types    ( anyTypeOfKind )

import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info ( RuleInfo( RuleInfo ) )
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Name ( Name, NamedThing(..), nameIsLocalOrFrom )
import CSlash.Types.Name.Set
import CSlash.Types.Name.Env
import CSlash.Types.Name.Occurrence( occNameFS )
import CSlash.Types.Unique.FM
import CSlash.Types.Tickish
import CSlash.Types.Basic

import CSlash.Data.FastString
import CSlash.Data.Maybe
import CSlash.Data.Bag
import CSlash.Data.List.SetOps( hasNoDups )

-- import CSlash.Utils.FV( filterFV, fvVarSet )
import CSlash.Utils.Misc as Utils
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Constants (debugIsOn)

import Data.List (sortBy, mapAccumL, isPrefixOf)
import Data.Function    ( on )
import Control.Monad    ( guard )

{-
Note [CSlash plumbind for rules]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Differences from GHC:
* We do need mg_rules in ModGuts:
  - We specialize imported functions, and put these auto-rules in the mg_rules
  - As of now, specialization is the first time we inhabit mg_rules
* We do not need md_rules in the HPT.
* eps_rule_base todo
-}

{- *********************************************************************
*                                                                      *
                   Specialization info about and Id
*                                                                      *
********************************************************************* -}

mkRule
  :: Module
  -> Bool
  -> RuleName
  -> Activation
  -> Name
  -> [CoreBndr]
  -> [CoreExpr]
  -> CoreExpr
  -> CoreRule
mkRule this_mod is_local name act fn bndrs args rhs
  = Rule { ru_name = name
         , ru_act = act
         , ru_fn = fn
         , ru_bndrs = bndrs
         , ru_args = args
         , ru_rhs = occurAnalyzeExpr rhs
         , ru_rough = roughTopNames args
         , ru_origin = this_mod
         , ru_orphan = orph
         , ru_local = is_local }
  where
    lhs_names = extendNameSet (orphNamesOfExprs args) fn

    local_lhs_names = filterNameSet (nameIsLocalOrFrom this_mod) lhs_names

    orph = chooseOrphanAnchor local_lhs_names

mkSpecRule
  :: DynFlags
  -> Module
  -> Activation
  -> SDoc
  -> CoreId
  -> [CoreBndr]
  -> [CoreExpr]
  -> CoreExpr
  -> CoreRule
mkSpecRule dflags this_mod inl_act herald fn bndrs args rhs
  = case idJoinPointHood fn of
      JoinPoint join_arity -> etaExpandToJoinPointRule join_arity rule
      NotJoinPoint -> rule
  where
    rule = mkRule this_mod is_local rule_name inl_act (varName fn) bndrs args rhs

    is_local = isLocalId fn
    rule_name = mkSpecRuleName dflags herald fn args

mkSpecRuleName :: DynFlags -> SDoc -> CoreId -> [CoreExpr] -> FastString
mkSpecRuleName dflags herald fn args
  = mkFastString $ showSDoc dflags $ herald <+> ftext (occNameFS (getOccName fn))
                                            <+> hsep (mapMaybe ppr_call_key_ty args)
  where
    ppr_call_key_ty :: CoreExpr -> Maybe SDoc
    ppr_call_key_ty (Type ty) = case getTyVar_maybe ty of
                                  Just {} -> Just (text "@_")
                                  Nothing -> Just $ char '@' <> pprParendType ty
    ppr_call_key_ty _ = Nothing

roughTopNames :: [CoreExpr] -> [Maybe Name]
roughTopNames args = map roughTopName args

roughTopName :: CoreExpr -> Maybe Name
roughTopName (Type ty) = case tcSplitTyConApp_maybe ty of
                           Just (tc, _) -> Just (getName tc)
                           Nothing -> Nothing
roughTopName (KiCo _) = Nothing
roughTopName (Kind _) = Nothing
roughTopName (App f _) = roughTopName f
roughTopName (Var f) | isGlobalId f, isDataConId f || idArity f > 0 = Just (varName f)
roughTopName (Tick t e) | tickishFloatable t = roughTopName e
roughTopName _ = Nothing

ruleCantMatch :: [Maybe Name] -> [Maybe Name] -> Bool
ruleCantMatch (Just n1 : ts) (Just n2 : as) = n1 /= n2 || ruleCantMatch ts as
ruleCantMatch (_ : ts) (_ : as) = ruleCantMatch ts as
ruleCantMatch _ _ = False

{- *********************************************************************
*                                                                      *
                        RuleInfo
*                                                                      *
********************************************************************* -}

extendRuleInfo :: RuleInfo -> [CoreRule] -> RuleInfo
extendRuleInfo (RuleInfo rs1 fvs1) rs2
  = RuleInfo (rs2 ++ rs2) (rulesFreeVarsDSets rs2 `unionFVs` fvs1)

addIdSpecializations :: CoreId -> [CoreRule] -> CoreId
addIdSpecializations id rules
  | null rules
  = id
  | otherwise
  = setIdSpecialization id $
    extendRuleInfo (idSpecialization id) rules

{- *********************************************************************
*                                                                      *
                        RuleBase
*                                                                      *
********************************************************************* -}

type RuleBase = NameEnv [CoreRule]

emptyRuleBase :: RuleBase
emptyRuleBase = emptyNameEnv

mkRuleBase :: [CoreRule] -> RuleBase
mkRuleBase rules = extendRuleBaseList emptyRuleBase rules

extendRuleBaseList :: RuleBase -> [CoreRule] -> RuleBase
extendRuleBaseList rule_base new_rules
  = foldl' extendRuleBase rule_base new_rules

extendRuleBase :: RuleBase -> CoreRule -> RuleBase
extendRuleBase rule_base rule
  = extendNameEnv_Acc (:) Utils.singleton rule_base (ruleIdName rule) rule

data RuleEnv = RuleEnv
  { re_local_rules :: !RuleBase
  , re_home_rules :: !RuleBase
  , re_eps_rules :: !RuleBase
  , re_visible_orphs :: !ModuleSet
  }

mkRuleEnv :: ModGuts -> RuleBase -> RuleBase -> RuleEnv
mkRuleEnv ModGuts{ mg_module = this_mod, mg_deps = deps, mg_rules = local_rules }
  eps_rules hpt_rules
  = RuleEnv { re_local_rules = mkRuleBase local_rules
            , re_home_rules = hpt_rules
            , re_eps_rules = eps_rules
            , re_visible_orphs = mkModuleSet vis_orphs }
  where
    vis_orphs = [this_mod] -- TODO: if add dep_orphs

{- *********************************************************************
*                                                                      *
                        Matching
*                                                                      *
********************************************************************* -}

lookupRule
  :: RuleOpts
  -> InScopeEnv
  -> (Activation -> Bool)
  -> CoreId
  -> [CoreExpr]
  -> [CoreRule]
  -> Maybe (CoreRule, CoreExpr)
lookupRule opts rule_env@(ISE in_scope _) is_active fn args rules
  = case go [] rules of
      [] -> Nothing
      (m:ms) -> Just (findBest in_scope (fn, args') m ms)
  where
    rough_args = roughTopNames args

    args' = map (stripTicksTopE tickishFloatable) args
    ticks = concatMap (stripTicksTopT tickishFloatable) args

    go :: [(CoreRule, CoreExpr)] -> [CoreRule] -> [(CoreRule, CoreExpr)]
    go ms [] = ms
    go ms (r:rs)
      | Just e <- matchRule opts rule_env is_active fn args' rough_args r
      = go ((r, mkTicks ticks e):ms) rs
      | otherwise
      = go ms rs

findBest
  :: TermSubstInScope
  -> (CoreId, [CoreExpr])
  -> (CoreRule, CoreExpr)
  -> [(CoreRule, CoreExpr)]
  -> (CoreRule, CoreExpr)
findBest _ _ (rule, ans) [] = (rule, ans)
findBest in_scope target (rule1, ans1) ((rule2, ans2) : prs) = panic "findBest unreachable?"
  -- | isMoreSpecific in_scope rule1 rule2 = findBest in_scope target (rule1, ans1) prs
  -- | isMoreSpecific in_scope rule2 rule1 = findBest in_scope target (rule2, ans1) prs
  -- | otherwise = panic "findBest rule overlap"

-- isMoreSpecific :: TermSubstInScope -> CoreRule -> CoreRule -> Bool
-- isMoreSpecific _ BuiltinRule{} _ = False
-- isMoreSpecific _ Rule{} BuiltinRule{} = True
-- isMoreSpecific in_scope Rule{ ru_bndrs = bndrs1, ru_args = args1 }
--                         Rule{ ru_bndrs = bndrs2, ru_args = args2 }
--   = isJust (matchExprs in_scope_env bndrs2 args2 args1)
--   where
--     full_in_scope = in_scope `extendTermSubstInScopeSetsList` bndrs1
--     in_scope_env = ISE full_in_scope noUnfoldingFun

matchRule
  :: RuleOpts
  -> InScopeEnv
  -> (Activation -> Bool)
  -> CoreId
  -> [CoreExpr]
  -> [Maybe Name]
  -> CoreRule
  -> Maybe CoreExpr
matchRule opts rule_env _ fn args _ BuiltinRule = panic "BuiltinRule"

matchRule _ rule_env is_active _ args rough_args Rule{ ru_name = rule_name
                                                     , ru_act = act
                                                     , ru_rough = tpl_tops
                                                     , ru_bndrs = tpl_vars
                                                     , ru_args = tpl_args
                                                     , ru_rhs = rhs }
  | not (is_active act) = Nothing
  | ruleCantMatch tpl_tops rough_args = Nothing
  | otherwise = panic "matchN rule_env rule_name tpl_vars tpl_args args rhs"

-- matchN
--   :: InScopeEnv
--   -> RuleName
--   -> [CoreBndr]
--   -> [CoreExpr]
--   -> [CoreExpr]
--   -> CoreExpr
--   -> Maybe CoreExpr
-- matchN ise _ tmpl_vars tmpl_es target_es rhs = do panic "match
  
-- matchExprs
--   :: InScopeEnv
--   -> [CoreBndr]
--   -> [CoreExpr]
--   -> [CoreExpr]
--   -> Maybe ()
-- matchExprs (ISE in_scope id_unf) tmpl_vars tmpl_es target_es = do
--   rule_subst <- match_expr init_menv emptyRuleSubst tmpl_es target_es
--   let (_, matched_es) = mapAccumL (lookup_tmpl rule_subst) (mkEmptyTermSubst in_scope) $
--                         tmpl_vars `zip` tmpl_vars1


-- match_exprs
--   :: RuleMatchEnv
--   -> RuleSubst
--   -> [CoreExpr]
--   -> [CoreExpr]
--   -> Maybe RuleSubst
-- match_exprs _ subst [] _ = Just subst
-- match_exprs renv subst (e1:es1) (e2:es2) = do
--   subst' <- match renv subst e1 e2
--   match_exprs renv subst' es1 es2
-- match_exprs _ _ _ _ = Nothing

-- {- *********************************************************************
-- *                                                                      *
--                    The main matcher
-- *                                                                      *
-- ********************************************************************* -}

-- data RuleMatchEnv = RV

-- data RuleSubst = RS

-- match
--   :: RuleMatchEnv
--   -> RuleSubst
--   -> CoreExpr
--   -> CoreExpr
--   -> MTypeCoercion Zk
--   -> Maybe RuleSubst
-- -- match renv subst e1 (Tick t e2) mco
-- --   | tickishFloatable t
-- --   = match renv subst' e1 e2 mco
-- --   | otherwise
-- --   = Nothing
-- --   where
-- --     subst' = subst { rs_binds = rs_binds subst . mkTick t }

-- -- match renv subst e@(Tick t e1) e2 mco
-- --   | tickishFloatable t
-- --   = match renv subst e1 e2 mco
-- --   | otherwise
-- --   = pprPanic "Tick in rule" (ppr e)

-- -- match renv subst (Type ty1) (Type ty2) MRefl
-- --   = match_ty renv subst ty1 ty2

-- -- match renv subst (KiCo co1) (KiCo co2) MRefl
-- --   = match_kico renv subst co1 co2

-- -- match renv subst (Kind ki) (Kind ki) MRefl
-- --   = match_ki renv subst ki1 ki2

-- -- match renv subst e1 (Cast e2 co2) mco
-- --   = match renv subst e1 e2 (checkReflexiveMCo (mkTransMCoR co2 mco))

-- -- match renv subst (Cast e1 co2) e2 mco
-- --   = matchTemplateCast renv subst e1 co1 e2 mco

-- -- match _ subst (Lit lit1) (Lit lit2) mco = panic "match lit"

-- -- match renv subst (Var v1) e2 mco
-- --   = match_var renv subst v1 (mkCastMCo e2 mco)

-- -- match renv subst e1 (Var v2) mco
-- --   | not (inRnEnvR rn_env v2)
-- --   , Just e2' <- expandUnfolding_maybe (rv_unf renv v2')
-- --   = match (renv { rv_lcl = nukeRnEnvR rn_env }) subst e1 e2' mco
-- --   where
-- --     v2' = lookupRnInScope rn_env v2
-- --     rn_env = rv_lcl renv

-- -- match renv@RV{ rv_tmpls = tmpls, rv_lcl = rn_env } subst e1@App{} e2 MRefl
-- --   | (Var f, args) <- collectArgs e1
-- --   , let f' = rnOccL rn_env f
-- --   , f' `elemVarSet` tmpls
-- --   , Just vs2 <- traverse arg_as_lcl_var args
-- --   , hasNoDups vs2
-- --   , not can_decompose_app_instead
-- --   = match_tmpl_var renv subst f' (mkCoreLams vs2 e2)
-- --   where
-- --     arg_as_lcl_var :: CoreExpr -> Maybe 
-- --     arg_as_lcl_var
-- --     arg_as_lcl_var

-- match _ _ _ _ _ = panic "match other"
