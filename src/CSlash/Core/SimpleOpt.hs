module CSlash.Core.SimpleOpt where

import CSlash.Cs.Pass

import CSlash.Core as Core
import CSlash.Core.Opt.Arity
import CSlash.Core.Subst
import CSlash.Core.Utils
import CSlash.Core.FVs
import CSlash.Core.Unfold
-- import CSlash.Core.Unfold.Make
import CSlash.Core.Make ( FloatBind(..), mkCoreLams, mkWildValBinder )
import CSlash.Core.Opt.OccurAnal( occurAnalyzeExpr, occurAnalyzePgm{-, zapLambdaBndrs-} )
import CSlash.Core.DataCon
-- import CSlash.Core.Coercion.Opt ( optCoercion, OptCoercionOpts (..) )
import CSlash.Core.Type
import CSlash.Core.Type.Compare
import CSlash.Core.Kind
import CSlash.Core.Predicate( isTyCoVarType )

import CSlash.Types.Literal
import CSlash.Types.Var.Class
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info ( realUnfoldingInfo, setUnfoldingInfo, {-setRuleInfo,-} IdInfo (..) )
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.Demand( {-etaConvertDmdSig,-} topSubDmd )
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

simpleOptPgm
  :: SimpleOpts
  -> Module
  -> CoreProgram
  -> (CoreProgram, CoreProgram)
simpleOptPgm opts this_mod binds = (reverse binds', occ_anald_binds)
  where
    occ_anald_binds = occurAnalyzePgm this_mod (const True) binds

    (final_env, binds') = foldl' do_one (emptyEnv opts, []) occ_anald_binds

    do_one (env, binds') bind = case simple_opt_bind env bind TopLevel of
                                  (env', Nothing) -> (env', binds')
                                  (env', Just bind') -> (env', bind' : binds')

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

soeSetInScope :: TermSubstInScope -> SimpleOptEnv -> SimpleOptEnv
soeSetInScope in_scope env@(SOE { soe_subst = subst })
  = env { soe_subst = setTermInScopeSets subst in_scope }

simple_opt_clo :: HasDebugCallStack => TermSubstInScope -> SimpleClo -> OutExpr
simple_opt_clo in_scope (e_env, e)
  = simple_opt_expr (soeSetInScope in_scope e_env) e

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
    go (KiCo kco) = KiCo (go_kco kco)
    go (Kind ki) = Kind (substMonoKiUnchecked subst ki)
    go (Lit lit) = Lit lit
    go (Tick tickish e) = mkTick (substTickish subst tickish) (go e)
    go (Cast e co) = mk_cast (go e) (go_tco co)
    go (Let bind body) = case simple_opt_bind env bind NotTopLevel of
                           (env', Nothing) -> simple_opt_expr env' body
                           (env', Just bind) -> Let bind (simple_opt_expr env' body)
    go lam@(Lam {}) = go_lam env [] lam
    go (Case e b ty as)
      | isDeadBinder b
      , Just (_, [], con, _, es) <- exprIsConApp_maybe in_scope_env e'
      , Just (Alt altcon bs rhs) <- findAlt (DataAlt con) as
      = case altcon of
          DEFAULT -> go rhs
          _ -> panic "foldr wrapLet (simple_opt_expr env' rhs) mb_prs"
            -- where
            --   (env', mb_prs) = mapAccumL (simple_out_bind NotTopLevel) env $ panic "zipEqual bs es"
      | otherwise
      = Case e' b' (substTyUnchecked subst ty) (map (go_alt env') as)
      where
        e' = go e
        (env', b', _) = subst_opt_id_bndr env b Nothing

    go_tco co = panic "optTyCoercion (so_co_opts (soe_opts env)) subst co"

    go_kco co = panic "optKiCoercion (so_co_opts (soe_opts env)) subst co"

    go_alt env (Alt con bndrs rhs)
      = Alt con bndrs' (simple_opt_expr env' rhs)
      where
        (env', bndrs') = subst_opt_id_bndrs env bndrs

    go_lam env bs' (Lam b mki e) = go_lam env' ((b', mki'):bs') e
      where (env', b', mki') = subst_opt_bndr env b mki
    go_lam env bs' e
      | so_eta_red (soe_opts env)
      , Just etad_e <- tryEtaReduce rec_ids bs e' topSubDmd = etad_e
      | otherwise = mkCoreLams bs e'
      where
        bs = reverse bs'
        e' = simple_opt_expr env e
      
mk_cast :: CoreExpr -> TypeCoercion Zk -> CoreExpr
mk_cast (Cast e co1) co2 = mk_cast e (co1 `mkTyTransCo` co2)
mk_cast (Tick t e) co = Tick t (mk_cast e co)
mk_cast e co | isReflexiveTyCo co = e
             | otherwise = Cast e co
-- TODO: check for other places to use isReflexiveTyCo instead of isReflTyCo

simple_app :: HasDebugCallStack => SimpleOptEnv -> InExpr -> [SimpleClo] -> CoreExpr
simple_app = panic "unfinished"

simple_opt_bind :: SimpleOptEnv -> InBind -> TopLevelFlag -> (SimpleOptEnv, Maybe OutBind)
simple_opt_bind = panic "unfinished"

safe_to_inline :: OccInfo -> Bool
safe_to_inline IAmALoopBreaker{} = False
safe_to_inline IAmDead = True
safe_to_inline OneOcc{ occ_in_lam = NotInsideLam, occ_n_br = 1 } = True
safe_to_inline OneOcc{} = False
safe_to_inline ManyOccs{} = False

do_beta_by_substitution :: CoreBndr -> CoreExpr -> Bool
do_beta_by_substitution (Core.Id bndr) rhs
  = panic "exprIsTrivial rhs" -- exprIsTrivial must do kind checking
    || safe_to_inline (idOccInfo bndr)
do_beta_by_substitution _ _ = False

do_case_elim :: CoreExpr -> CoreId -> [CoreId] -> Bool
do_case_elim scrut case_bndr alt_bndrs = panic "do_case_elim"

simple_out_bind
  :: TopLevelFlag
  -> SimpleOptEnv
  -> (InVar, OutExpr)
  -> (SimpleOptEnv, Maybe (OutVar, OutExpr))
simple_out_bind = panic "unfinished"

subst_opt_bndrs :: SimpleOptEnv -> [InVar] -> (SimpleOptEnv, [OutVar])
subst_opt_bndrs env bndrs = mapAccumL (\s v -> fst2Of3 $ subst_opt_bndr s v Nothing) env bndrs
  where
    fst2Of3 (a, b, _) = (a, b)

subst_opt_id_bndrs :: SimpleOptEnv -> [InId] -> (SimpleOptEnv, [OutId])
subst_opt_id_bndrs env bndrs
  = mapAccumL (\s v -> fst2Of3 $ subst_opt_id_bndr s v Nothing) env bndrs
  where
    fst2Of3 (a, b, _) = (a, b)

subst_opt_bndr
  :: SimpleOptEnv
  -> InVar
  -> Maybe (MonoKind Zk)
  -> (SimpleOptEnv, OutVar, Maybe (MonoKind Zk))
subst_opt_bndr env (Core.Id id) mki = case subst_opt_id_bndr env id mki of
  (a, b, c) -> (a, Core.Id b, c)
subst_opt_bndr env (Tv tv) Nothing
  = let (subst', tv') = substTyVarBndr (soe_subst env) tv
    in (env { soe_subst = subst' }, Tv tv', Nothing)
subst_opt_bndr env (KCv kcv) Nothing
  = let (subst', kcv') = substKiCoVarBndr (soe_subst env) kcv
    in (env { soe_subst = subst' }, KCv kcv', Nothing)
subst_opt_bndr env (Kv kv) Nothing
  = let (subst', kv') = substKiVarBndr (soe_subst env) kv
    in (env { soe_subst = subst' }, Kv kv', Nothing)
subst_opt_bndr _ bndr ki = pprPanic "subst_opt_bndr fun kind mismathc" (ppr bndr $$ ppr ki)

subst_opt_id_bndr
  :: SimpleOptEnv
  -> InId
  -> Maybe (MonoKind Zk)
  -> (SimpleOptEnv, OutId, Maybe (MonoKind Zk))
subst_opt_id_bndr env@(SOE { soe_subst = subst, soe_inl = inl }) old_id old_fun_ki
  = (env { soe_subst = new_subst, soe_inl = new_inl}, new_id, new_fun_ki)
  where
    in_scope@(id_in_scope, _, _, _, _) = substInScopeSets subst
    id1 = uniqAway id_in_scope old_id
    id2 = updateVarType (substTyUnchecked subst) id1
    new_id = zapFragileIdInfo id2
    new_fun_ki = substMonoKi subst <$> old_fun_ki -- maybe substMonoKiUnchecked?

    new_id_in_scope = case in_scope of
      (id, _, _, _, _) -> id `extendInScopeSet` new_id

    no_change = new_id == old_id

    new_id_subst
      | no_change = delVarEnv (id_env subst) old_id
      | otherwise = extendVarEnv (id_env subst) old_id (Var new_id)

    new_subst = subst { id_in_scope = new_id_in_scope
                      , id_env = new_id_subst }
    new_inl = delVarEnv inl old_id

-- wrapLet :: Maybe (Id Zk, CoreExpr) -> CoreExpr -> CoreExpr
-- wrapLet Nothing body = body
-- wrapLet (Just (b, r)) body = Let (NonRec b r) body

{- *********************************************************************
*                                                                      *
         exprIsConApp_maybe
*                                                                      *
********************************************************************* -}

data ConCont = CC [CoreExpr] (MTypeCoercion Zk)

exprIsConApp_maybe
  :: HasDebugCallStack
  => InScopeEnv
  -> CoreExpr
  -> Maybe (TermSubstInScope, [FloatBind], DataCon Zk, [Type Zk], [CoreExpr])
exprIsConApp_maybe ise@(ISE in_scope id_unf) expr
  = go (Left in_scope) [] expr (CC [] MRefl)
  where
    go :: Either TermSubstInScope CoreSubst
      -> [FloatBind] -> CoreExpr -> ConCont
      -> Maybe (TermSubstInScope, [FloatBind], DataCon Zk, [Type Zk], [CoreExpr])
    go subst floats (Tick t expr) cont
      | not (tickishIsCode t) = panic "unreachable"
    go subst floats (Cast expr co1) (CC args m_co2)
      | Just (args', m_co1') <- pushCoArgs (subst_tco subst co1) args
      = go subst floats expr (CC args' (panic "m_co1' `mkTransMTyCo` m_co2"))
    go subst floats (App fun arg) (CC args mco)
      | isValArg arg && needsCaseBinding arg
      , (subst', float, bndr) <- case_bind subst arg (exprType arg)
      = go subst' (float:floats) fun (CC (Var bndr : args) mco)
      | otherwise
      = go subst floats fun (CC (subst_expr subst arg : args) mco)
    go subst floats (Lam bndr mki body) (CC (arg:args) mco)
      | do_beta_by_substitution bndr arg
      = go (extend subst bndr arg) floats body (CC args mco)
      | otherwise
      = let (subst', bndr') = subst_bndr subst bndr
            float = FloatLet (NonRec bndr' arg)
        in go subst' (float:floats) body (CC args mco)
    go subst floats (Let (NonRec bndr rhs) expr) cont
      | not (isJoinId bndr)
      = let rhs' = subst_expr subst rhs
            (subst', bndr') = subst_bndr subst bndr
            float = FloatLet (NonRec bndr' rhs')
        in go subst' (float:floats) expr cont
    go subst floats (Case scrut b _ [Alt con vars expr]) cont
      | do_case_elim scrut' b vars
      = go (extend subst (Core.Id b) scrut') floats expr cont
      | otherwise
      = let (subst', b') = subst_bndr subst b
            (subst'', vars') = subst_bndrs subst' vars
            scrut' = subst_expr subst scrut
            float = FloatCase scrut' b' con vars'
        in go subst'' (float:floats) expr cont
      where
        scrut' = subst_expr subst scrut
    go (Right sub) floats (Var v) cont
      = go (Left (substInScopeSets sub))
           floats
           (lookupIdSubst sub v)
           cont
    go (Left in_scope) floats (Var fun) cont@(CC args mco)
      | Just con <- isDataConId_maybe fun
      , count isValArg args == idArity fun
      , (in_scope', seq_floats, args') <- mkFieldSeqFloats in_scope con args
      = succeedWith in_scope' (seq_floats ++ floats) $
        pushCoDataCon con args' mco

      | idArity fun == 0
      , Just rhs <- expandUnfolding_maybe unfolding
      = let in_scope' = extend_in_scope (exprFreeVars rhs)
        in  go (Left in_scope') floats rhs cont

      -- TODO: handle LitString here? What about overlitstring

      where
        unfolding = id_unf fun
        extend_in_scope unf_fvs
          | isLocalId fun = in_scope `extendTermSubstInScopeSetsSets` unf_fvs
          | otherwise = in_scope

    go _ _ _ _ = Nothing 

    succeedWith
      :: TermSubstInScope
      -> [FloatBind]
      -> Maybe (DataCon Zk, [Type Zk], [CoreExpr])
      -> Maybe (TermSubstInScope, [FloatBind], DataCon Zk, [Type Zk], [CoreExpr])
    succeedWith in_scope rev_floats x = do
      (con, tys, args) <- x
      let floats = reverse rev_floats
      return (in_scope, floats, con, tys, args)

    subst_in_scope :: Either TermSubstInScope CoreSubst -> TermSubstInScope
    subst_in_scope (Left in_scope) = in_scope
    subst_in_scope (Right s) = substInScopeSets s

    subst_extend_in_scope
      :: Either TermSubstInScope CoreSubst
      -> Id Zk
      -> Either TermSubstInScope CoreSubst
    subst_extend_in_scope (Left in_scope) v = Left (extendTermSubstInScopeSet in_scope v)
    subst_extend_in_scope (Right s) v = Right (extendTermSubstInScope s (Core.Id v))

    subst_tco Left{} co = co
    subst_tco (Right s) co = panic "substTyCo s co"

    subst_expr Left{} e = e
    subst_expr (Right s) e = panic "substExpr s e"

    subst_bndr msubst bndr
      = (Right subst', bndr')
      where
        (subst', bndr') = panic "substBndr subst bndr"
        subst = case msubst of
          Left in_scope -> mkEmptyTermSubstIS in_scope
          Right subst -> subst

    subst_bndrs subst bs = mapAccumL subst_bndr subst bs

    extend
      :: Either TermSubstInScope CoreSubst
      -> CoreBndr
      -> CoreExpr
      -> Either TermSubstInScope CoreSubst
    extend (Left in_scope) v e = Right (extendSubst (mkEmptyTermSubstIS in_scope) v e)
    extend (Right s) v e = Right (extendSubst s v e)

    case_bind
      :: Either TermSubstInScope CoreSubst
      -> CoreExpr
      -> Type Zk
      -> (Either TermSubstInScope CoreSubst, FloatBind, Id Zk)
    case_bind subst expr expr_ty = (subst', float, bndr)
      where
        bndr = setCaseBndrEvald $
               uniqAway (fstOf5 $ subst_in_scope subst) $
               mkWildValBinder expr_ty
        subst' = subst_extend_in_scope subst bndr
        expr' = subst_expr subst expr
        float = FloatCase expr' bndr DEFAULT []
        fstOf5 (a, _, _, _, _) = a

    mkFieldSeqFloats
      :: TermSubstInScope
      -> DataCon Zk
      -> [CoreExpr]
      -> (TermSubstInScope, [FloatBind], [CoreExpr])
    mkFieldSeqFloats in_scope dc args
      = (in_scope', floats', ty_args ++ val_args')
      where
        (ty_args, val_args) = break isValArg args
        (in_scope', floats', val_args') = foldr do_one (in_scope, [], []) val_args
        do_one arg (in_scope, floats, args)
          | exprIsHNF arg = no_seq
          | otherwise = (in_scope', float:floats, Var bndr : args)
          where
            no_seq = (in_scope, floats, arg:args)
            (in_scope', float, bndr) = case case_bind (Left in_scope) arg (exprType arg) of
              (Left in_scope', float, bndr) -> (in_scope', float, bndr)
              _ -> panic "unreachable"

