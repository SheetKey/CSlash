module CSlash.Core.SimpleOpt where

import CSlash.Cs.Pass

import CSlash.Core
-- import CSlash.Core.Opt.Arity
import CSlash.Core.Subst
import CSlash.Core.Utils
import CSlash.Core.FVs
import CSlash.Core.Unfold
-- import CSlash.Core.Unfold.Make
-- import CSlash.Core.Make ( FloatBind(..) )
import CSlash.Core.Opt.OccurAnal( occurAnalyzeExpr{-, occurAnalysePgm, zapLambdaBndrs-} )
import CSlash.Core.DataCon
-- import CSlash.Core.Coercion.Opt ( optCoercion, OptCoercionOpts (..) )
import CSlash.Core.Type
import CSlash.Core.Predicate( isTyCoVarType )

import CSlash.Types.Literal
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info ( realUnfoldingInfo, setUnfoldingInfo, {-setRuleInfo,-} IdInfo (..) )
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
-- import CSlash.Types.Demand( etaConvertDmdSig, topSubDmd )
import CSlash.Types.Tickish
import CSlash.Types.Basic

import CSlash.Builtin.Types
import CSlash.Builtin.Names

import CSlash.Unit.Module ( Module )
import CSlash.Utils.Encoding
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc

import CSlash.Data.Maybe       ( orElse )
import CSlash.Data.Graph.UnVar
import Data.List (mapAccumL)
import qualified Data.ByteString as BS


{- *********************************************************************
*                                                                      *
        The Simple Optimiser
*                                                                      *
********************************************************************* -}

data SimpleOpts = SimpleOpts
  { so_uf_opts :: !UnfoldingOpts
  -- TODO: , so_co_opts :: !OptCoercionOpts
  , so_eta_red :: !Bool
  , so_inline :: !Bool
  }

simpleOptExpr :: HasDebugCallStack => SimpleOpts -> CoreExpr -> CoreExpr
simpleOptExpr opts expr = simpleOptExprWith opts init_subst expr
  where
    fvs = case exprFreeVars expr of
            (ids, tcs, tvs, kcvs, ks) -> (mapVarSet zapIdUnfolding ids, tcs, tvs, kcvs, ks)
    init_subst = mkEmptyTermSubst fvs
            
simpleOptExprWith :: HasDebugCallStack => SimpleOpts -> CoreSubst -> InExpr -> OutExpr
simpleOptExprWith opts subst expr
  = simple_opt_expr init_env (occurAnalyzeExpr expr)
  where
    init_env = (emptyEnv opts) { soe_subst = subst }

type SimpleClo = (SimpleOptEnv, InExpr)

data SimpleOptEnv = SOE
  { soe_opts :: {-# UNPACK #-} !SimpleOpts
  , soe_inl :: VarEnv (Id Zk) SimpleClo
  , soe_subst :: CoreSubst
  , soe_rec_ids :: !UnVarSet
  }

instance Outputable SimpleOptEnv where
  ppr (SOE { soe_inl = inl, soe_subst = subst })
    = text "SOE {" <+> vcat [ text "soe_inl =" <+> ppr inl
                            , text "soe_subst =" <+> ppr subst ]
      <+> text "}"

emptyEnv :: SimpleOpts -> SimpleOptEnv
emptyEnv opts = SOE { soe_inl = emptyVarEnv
                    , soe_subst = emptySubst
                    , soe_rec_ids = emptyUnVarSet
                    , soe_opts = opts }

simple_opt_expr :: HasDebugCallStack => SimpleOptEnv -> InExpr -> OutExpr
simple_opt_expr env expr = go expr
  where
    rec_ids = soe_rec_ids env
    subst = soe_subst env
    in_scope = substInScopeSets subst
    in_scope_env = ISE in_scope alwaysActiveUnfoldingFun

    go (Var v)
      | Just clo <- lookupVarEnv (soe_inl env) v
      = simple_opt_clo in_scope clo
      | otherwise
      = lookupIdSubst subst v
    go (App e1 e2) = simple_app env e1 [(env, e2)]
    go (Type ty) = Type (substTyUnchecked subst ty)
    go (KiCo kco) = KiCo (go_kco co)
    go (Kind ki) = Kind (substMonoKiUnchecked subst ki)
    go (Lit lit) = Lit lit
    go (Tick tickish e) = mkTick (substTickish subst tickish) (go e)
    go (Cast e co) = mk_cast (go e) (go_tco co)
    go (Let bind body) = case simple_opt_bind env binds NotTopLevel of
                           (env', Nothing) -> simple_op_expr env' body
                           (env', Just bind) -> Let bind (simple_opt_expr env' body)
    go lam@(Lam {}) = go_lam env [] lam
    go (Case e b ty as)
      | isDeadBinder b
      , Just (_, [], con, _, es) <- exprIsConApp_maybe in_scope_env e'
      , Just (Alt altcon bs rhs) <- findAlt (DataAlt con) as
      = case altcon of
          DEFAULT -> go rhs
          _ -> foldr wrapLet (simple_opt_expr env' rhs) mb_prs
            where
              (env', mb_prs) = mapAccumL (simple_out_bind NotTopLevel) env $ zipEqual bs es
      | otherwise
      = Case e' b' (substTyUnchecked subst ty) (map (go_alt env') as)
      where
        e' = go e
        (env', b') = subst_opt_bndr env b

    go_tco co = optTyCoercion (so_co_opts (soe_opts env)) subst co

    go_kco co = optKiCoercion (so_co_opts (soe_opts env)) subst co

    go_alt env (Alt con bndrs rhs)
      = Alt con bndrs' (simple_opt_expr env' rhs)
      where
        (env', bndrs') = subst_opt_bndrs env bndrs

    go_lam env bs' (Lam b mki e) = go_lam env' (b':bs') e
      where (env', b') = subst_opt_bndr env b
    go_lam env bs' e
      | so_eta_red (soe_opts env)
      , Just etad_e <- tryEtaReduce rec_ids bs e' topSubDmd = etad_e
      | otherwise = mkLams bs e'
      where
        bs = reverse bs'
        e' = simple_opt_expr env e
      
mk_cast :: CoreExpr -> TypeCoercion Zk -> CoreExpr
mk_cast (Cast e co1) co2 = mk_cast e (co1 `mkTransCo` co2)
mk_cast (Tick t e) co = Tick t (mk_cast e co)
mk_cast e co | isReflexiveTyCo co = e
             | otherwise = Cast e co
-- TODO: check for other places to use isReflexiveTyCo instead of isReflTyCo

simple_app :: HasDebugCallStack => SimpleOptEnv -> InExpr -> [SimpleClo] -> CoreExpr
simple_app = panic "unfinished"
