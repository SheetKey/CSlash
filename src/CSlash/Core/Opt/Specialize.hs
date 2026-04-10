{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}

module CSlash.Core.Opt.Specialize where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Driver.DynFlags
import CSlash.Driver.Config
import CSlash.Driver.Config.Diagnostic
import CSlash.Driver.Config.Core.Rules ( initRuleOpts )

import CSlash.Core.Type
import CSlash.Core.Kind
-- import CSlash.Core.SimpleOpt( defaultSimpleOpts, simpleOptExprWith )
import CSlash.Core.Predicate
import CSlash.Core.Opt.Monad
import qualified CSlash.Core.Subst as Core
import CSlash.Core.Subst (Subst(..), substTickish)
import CSlash.Core.Unfold.Make
import CSlash.Core as C
import CSlash.Core.Make
import CSlash.Core.Unify ( tcMatchTy )
import CSlash.Core.Rules
import CSlash.Core.Utils     ( exprIsTrivial, exprIsTopLevelBindable
                             , mkCast, exprType
                             , stripTicksTop{-, mkInScopeSetBndrs-} )
import CSlash.Core.FVs
import CSlash.Core.Type.FVs ( varsOfTypeList )
-- import GHC.Core.Opt.Arity( collectBindersPushingCo )
-- import GHC.Core.Ppr( pprIds )

-- import GHC.Builtin.Types  ( unboxedUnitTy )

import CSlash.Data.Maybe     ( maybeToList, isJust, mapMaybe )
import CSlash.Data.Bag
import CSlash.Data.OrdList
import CSlash.Data.List.SetOps

import CSlash.Types.Basic
import CSlash.Types.Unique.Supply
import CSlash.Types.Unique.DFM
import CSlash.Types.Name hiding (varName)
import CSlash.Types.Tickish
import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Error

import CSlash.Utils.Error ( mkMCDiagnostic )
import CSlash.Utils.Monad ( foldlM )
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Trace

import CSlash.Unit.Module( Module )
import CSlash.Unit.Module.ModGuts
import CSlash.Core.Unfold

import Data.List( partition )
import Data.List.NonEmpty ( NonEmpty (..) )

{- *********************************************************************
*                                                                      *
        The exported function
*                                                                      *
********************************************************************* -}

specProgram :: ModGuts -> CoreM ModGuts
specProgram guts@ModGuts { mg_module = this_mod, mg_rules = local_rules, mg_binds = binds } = do
  dflags <- getDynFlags
  rule_env <- initRuleEnv guts

  let top_env = SE { se_subst = Core.extendTermSubstInScopeBndrs Core.emptySubst binds
                   , se_module = this_mod
                   , se_rules = rule_env
                   , se_dflags = dflags }

      go [] = return ([], emptyUDs)
      go (bind:binds) = do
        (bind', binds', uds') <- specBind TopLevel top_env bind $ \_ -> go binds
        return (bind' ++ binds', uds')

  (binds', uds) <- runSpecM (go binds)

  panic "specProgram unfinished"

{- *********************************************************************
*                                                                      *
                   Specialising imported functions
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
                   specExpr
*                                                                      *
********************************************************************* -}

data SpecEnv = SE
  { se_subst :: Core.CoreSubst
  , se_module :: Module
  , se_rules :: RuleEnv
  , se_dflags :: DynFlags
  }

instance Outputable SpecEnv where
  ppr (SE { se_subst = subst }) = text "SE" <+> braces (text "subst =" <+> ppr subst)

specVar :: SpecEnv -> InId -> SpecM (OutExpr, UsageDetails)
specVar env@SE{ se_subst = Subst {..} } v
  | not (isLocalId v) = return (Var v, emptyUDs)
  | Just e <- lookupVarEnv id_env v = specExpr (zapSubst env) e
  | Just v' <- lookupInScope id_in_scope v = return (Var v', emptyUDs)
  | otherwise = pprPanic "specVar" (ppr v $$ ppr id_in_scope)

specExpr :: SpecEnv -> CoreExpr -> SpecM (CoreExpr, UsageDetails)

specExpr env (Var v) = specVar env v
specExpr env (Type ty) = return (Type (substTy env ty), emptyUDs)
specExpr env (KiCo co) = return (KiCo (substKiCo env co), emptyUDs)
specExpr env (Kind ki) = return (Kind (substKi env ki), emptyUDs)
specExpr _ (Lit lit) = return (Lit lit, emptyUDs)
specExpr env (Cast e co) = do
  (e', uds) <- specExpr env e
  return ((mkCast e' (panic "substTyCo env co")), uds)
specExpr env (Tick tickish body) = do
  (body', uds) <- specExpr env body
  return (Tick (specTickish env tickish) body', uds)
  
specExpr env expr@(App {}) = do
  let (fun_in, args_in) = collectArgs expr
  (args_out, uds_args) <- mapAndCombineSM (specExpr env) args_in
  let env_args = env
      (fun_in', args_out') = (fun_in, args_out)
  (fun_out', uds_fun) <- specExpr env fun_in'
  let uds_call = mkCallUDs env fun_out' args_out'
  return (fun_out' `mkCoreApps` args_out', uds_fun `thenUDs` uds_call `thenUDs` uds_args)

specExpr env e@Lam{} = specLam env' bndrs' body
  where
    (bndrs, body) = collectBinders e
    (env', bndrs') = substLamBndrs env bndrs

specExpr env (Case scrut case_bndr ty alts) = do
  (scrut', scrut_uds) <- specExpr env scrut
  (scrut'', case_bndr', alts', alts_uds) <- specCase env scrut' case_bndr alts
  return ( Case scrut'' case_bndr' (substTy env ty) alts'
         , scrut_uds `thenUDs` alts_uds )

specExpr env (Let bind body) = do
  (binds', body', uds) <- specBind NotTopLevel env bind $ \body_env -> specExpr body_env body
  return (foldr Let body' binds', uds)

specLam :: SpecEnv -> [(OutBndr, Maybe CoreMonoKind)] -> InExpr -> SpecM (OutExpr, UsageDetails)
specLam env bndrs body
  | null bndrs
  = specExpr env body
  | otherwise
  = do (body', uds) <- specExpr env body
       let free_uds = dumpUDs (fst <$> bndrs) uds
       return (mkCoreLams bndrs body', free_uds)

specTickish :: SpecEnv -> CoreTickish -> CoreTickish
specTickish SE{ se_subst = subst } bp = substTickish subst bp

specCase
  :: SpecEnv
  -> OutExpr
  -> InId
  -> [InAlt]
  -> SpecM (OutExpr, OutId, [OutAlt], UsageDetails)
specCase env scrut case_bndr alts = do
  (alts', uds_alts) <- mapAndCombineSM spec_alt alts
  return (scrut, case_bndr', alts', uds_alts)
  where
    (env_alt, case_bndr') = substLetBndr env case_bndr

    spec_alt (Alt con args rhs) = do
      (rhs', uds) <- specExpr env_rhs rhs
      let free_uds = dumpUDs (C.Id <$> case_bndr' : args') uds
      return (Alt con args' rhs', free_uds)
      where
        (env_rhs, args') = substLetBndrs env_alt args

{- *********************************************************************
*                                                                      *
                   Bindings
*                                                                      *
********************************************************************* -}

specBind
  :: TopLevelFlag
  -> SpecEnv
  -> InBind
  -> (SpecEnv -> SpecM (body, UsageDetails))
  -> SpecM ([OutBind], body, UsageDetails)
specBind top_lvl env (NonRec fn rhs) do_body = do
  (rhs', rhs_uds) <- specExpr env rhs

  (body_env1, fn1) <- case top_lvl of
    TopLevel -> return (env, fn)
    NotTopLevel -> cloneLetBndrSM env fn

  let fn2 | isStableUnfolding (idUnfolding fn1) = fn1
          | otherwise = fn1 `setIdUnfolding` mkSimpleUnfolding defaultUnfoldingOpts rhs'

      fn3 = floatifyIdDemandInfo fn2

      body_env2 = body_env1 `extendInScope` fn3

  (body', body_uds) <- do_body body_env2

  (fn4, spec_defns, body_uds1) <- specDefn env body_uds fn3 rhs

  let free_uds = dumpBindUDs [fn4] body_uds
      all_free_uds = free_uds `thenUDs` rhs_uds

      pairs = spec_defns ++ [(fn4, rhs')]

      final_binds = [NonRec b r | (b, r) <- pairs]

  return (final_binds, body', all_free_uds)

specBind top_lvl env (Rec pairs) do_body = do
  let (bndrs, rhss) = unzip pairs
  (rec_env, bndrs1) <- case top_lvl of
                         TopLevel -> return (env, bndrs)
                         NotTopLevel -> cloneRecBndrsSM env bndrs

  (rhss', rhs_uds) <- mapAndCombineSM (specExpr rec_env) rhss
  (body', body_uds) <- do_body rec_env

  let scope_uds = body_uds `thenUDs` rhs_uds

  (bndrs2, spec_defns2, uds2) <- specDefns rec_env scope_uds (bndrs1 `zip` rhss)

  (bndrs3, spec_defns3, uds3)
    <- if null spec_defns2
       then return (bndrs2, [], uds2)
       else do (bndrs3, spec_defns3, uds3) <- specDefns rec_env uds2 (bndrs2 `zip` rhss)
               return (bndrs3, spec_defns3 ++ spec_defns2, uds3)

  let final_uds = dumpBindUDs bndrs1 uds3
      final_bind = spec_defns3 ++ zip bndrs3 rhss'

  return ([Rec final_bind], body', final_uds)

specDefns
  :: SpecEnv
  -> UsageDetails
  -> [(OutId, InExpr)]
  -> SpecM ([OutId], [(OutId, OutExpr)], UsageDetails)
specDefns _ uds [] = return ([], [], uds)
specDefns env uds ((bndr, rhs) : pairs) = do
  (bndrs1, spec_defns1, uds1) <- specDefns env uds pairs
  (bndr1, spec_defns2, uds2) <- specDefn env uds1 bndr rhs
  return (bndr1 : bndrs1, spec_defns1 ++ spec_defns2, uds2)

specDefn
  :: SpecEnv
  -> UsageDetails
  -> OutId
  -> InExpr
  -> SpecM (CoreId, [(CoreId, CoreExpr)], UsageDetails)
specDefn env body_uds fn rhs = do
  let (body_uds_without_me, calls_for_me) = callsForMe fn body_uds
      rules_for_me = idCoreRules fn

  (rules, spec_defns, spec_uds)
    <- specCalls False env rules_for_me calls_for_me fn rhs

  return ( fn `addIdSpecializations` rules
         , spec_defns
         , body_uds_without_me `thenUDs` spec_uds)

type SpecInfo = ([CoreRule], [(CoreId, CoreExpr)], UsageDetails)

specCalls
  :: Bool
  -> SpecEnv
  -> [CoreRule]
  -> [CallInfo]
  -> OutId
  -> InExpr
  -> SpecM SpecInfo
specCalls spec_imp env existing_rules calls_for_me fn rhs
  | notNull calls_for_me
    && not (isNeverActive (idInlineActivation fn))
  = foldlM spec_call ([], [], emptyUDs) calls_for_me

  | otherwise
  = warnPprTrace (not (exprIsTrivial rhs) && notNull calls_for_me)
    "Missed specialization opportunity for" (ppr fn $$ trace_doc)
    $ return ([], [], emptyUDs)
  where
    trace_doc = panic "sep [ ppr rhs_bndrs, ppr (idInlineActivation fn) ]"

    fn_type = varType fn
    fn_arity = idArity fn
    fn_unf = realIdUnfolding fn
    inl_prag = idInlinePragma fn
    inl_act = inlinePragmaActivation inl_prag
    is_local = isLocalId fn
    dflags = se_dflags env
    this_mod = se_module env

    (rhs_bndrs, rhs_body) = panic "collectBindersPushingCo rhs"

    already_covered :: SpecEnv -> [CoreRule] -> [CoreExpr] -> Bool
    already_covered env new_rules args
      = isJust (specLookupRule env fn args (beginPhase inl_act) (new_rules ++ existing_rules))

    spec_call :: SpecInfo -> CallInfo -> SpecM SpecInfo
    spec_call spec_acc@(rules_acc, pairs_acc, uds_acc) CI{ ci_key = call_args } = do
      let all_call_args = call_args

          saturating_call_args = call_args ++ map mk_extra_arg (dropList call_args rhs_bndrs)

          mk_extra_arg C.Id{} = UnspecArg
          mk_extra_arg Tv{} = UnspecType
          mk_extra_arg KCv{} = UnspecKiCo
          mk_extra_arg Kv{} = UnspecKind

      (rhs_env2
        , leftover_bndrs
        , rule_bndrs
        , rule_lhs_args
        , spec_bndrs1
        , spec_args) <- specHeader env rhs_bndrs all_call_args

      if already_covered rhs_env2 rules_acc rule_lhs_args
        then return spec_acc
        else do (rhs_body', rhs_uds) <- specExpr rhs_env2 rhs_body
                let spec_rhs_bndrs = spec_bndrs1 ++ leftover_bndrs
                    spec_uds = dumpUDs (fst <$> spec_rhs_bndrs) rhs_uds
                    spec_rhs1 = mkCoreLams spec_rhs_bndrs rhs_body'

                    spec_fn_ty1 = exprType spec_rhs1

                    (spec_bndrs, spec_rhs, spec_fn_ty)
                      = (spec_bndrs1, spec_rhs1, spec_fn_ty1)

                    join_arity_decr = length rule_lhs_args - length spec_bndrs

                    simpl_opts = initSimpleOpts dflags
                    wrap_unf_body body = body `mkCoreApps` spec_args
                    spec_unf = panic "specUnfolding simpl_opts spec_bndrs"
                               -- wrap_unf_body rule_lhs_args fn_unf

                    arity_decr = count isValArg rule_lhs_args
                                 - count (isRuntimeVar . fst) spec_bndrs

                    spec_inl_prag
                      | not is_local
                      , isStrongLoopBreaker (idOccInfo fn)
                      = neverInlinePragma
                      | otherwise
                      = inl_prag

                    spec_fn_info = vanillaIdInfo `setArityInfo` max 0 (fn_arity - arity_decr)
                                                 `setInlinePragInfo` spec_inl_prag
                                                 `setUnfoldingInfo` spec_unf

                    spec_fn_details = case idDetails fn of
                                        JoinId join_arity -> JoinId (join_arity - join_arity_decr)
                                        _ -> VanillaId

                spec_fn <- newSpecIdSM (varName fn) spec_fn_ty spec_fn_details spec_fn_info

                let herald | spec_imp = text "SPEC/" <> ppr this_mod
                           | otherwise = text "SPEC"

                    spec_rule = mkSpecRule dflags this_mod inl_act
                                herald fn rule_bndrs rule_lhs_args
                                (mkAbsVarApps (Var spec_fn) spec_bndrs)

                return ( spec_rule : rules_acc
                       , (spec_fn, spec_rhs) : pairs_acc
                       , spec_uds `thenUDs` uds_acc
                       )

specLookupRule
  :: SpecEnv
  -> CoreId
  -> [CoreExpr]
  -> CompilerPhase
  -> [CoreRule]
  -> Maybe (CoreRule, CoreExpr)
specLookupRule env fn args phase rules
  = lookupRule ropts in_scope_env is_active fn args rules
  where
    dflags = se_dflags env
    in_scope = Core.substInScopeSets (se_subst env)
    in_scope_env = ISE in_scope (whenActiveUnfoldingFun is_active)
    ropts = initRuleOpts dflags
    is_active = isActive phase

{- *********************************************************************
*                                                                      *
                   SpecArg, and specHeader
*                                                                      *
********************************************************************* -}

data SpecArg
  = SpecType CoreType
  | UnspecType
  | UnspecKiCo
  | UnspecKind
  | UnspecArg

instance Outputable SpecArg where
  ppr (SpecType t) = text "SpecType" <+> ppr t
  ppr UnspecType = text "UnspecType"
  ppr UnspecKiCo = text "UnspecKiCoo"
  ppr UnspecKind = text "UnspecKind"
  ppr UnspecArg = text "UnspecArg"

isSpecUseful :: SpecArg -> Bool
isSpecUseful (SpecType _) = True
isSpecUseful _ = False

specHeader
  :: SpecEnv
  -> [(InBndr, Maybe CoreMonoKind)]
  -> [SpecArg]
  -> SpecM ( SpecEnv
           , [(OutBndr, Maybe CoreMonoKind)]
           , [OutBndr]
           , [OutExpr]
           , [(OutBndr, Maybe CoreMonoKind)]
           , [OutExpr] )
specHeader env ((Tv bndr, Nothing) : bndrs) (SpecType ty : args) = do
  let in_scope = Core.substInScopeSets (se_subst env)
      qvars0 = filterOut (`Core.elemInScopeSets` in_scope) $ to_bndrs $ varsOfTypeList ty
      qvars = (, Nothing) <$> qvars0
      (env1, qvars') = substLamBndrs env qvars
      ty' = substTy env1 ty
      env2 = extendTvSubst env1 bndr ty'
  (env3, leftover_bndrs, rule_bs, rule_es, bs', spec_args)
    <- specHeader env2 bndrs args

  pure ( env3
       , leftover_bndrs
       , (fst <$> qvars') ++ rule_bs
       , Type ty' : rule_es
       , qvars' ++ bs'
       , Type ty' : spec_args
       )
  where
    to_bndrs (tvs, kcvs, kvs) = (Kv <$> kvs) ++ (KCv <$> kcvs) ++ (Tv <$> tvs)

specHeader env (bndr@(Tv{}, Nothing) : bndrs) (UnspecType : args) = do
  let (env', bndr') = substLamBndr env bndr
  (env'', leftover_bndrs, rule_bs, rule_es, bs', spec_args)
    <- specHeader env' bndrs args
  pure ( env''
       , leftover_bndrs
       , fst bndr' : rule_bs
       , bndrToCoreExpr (fst bndr') : rule_es
       , bndr' : bs'
       , bndrToCoreExpr (fst bndr') : spec_args
       )

specHeader env (bndr@(KCv{}, Nothing) : bndrs) (UnspecKiCo : args) = do
  let (env', bndr') = substLamBndr env bndr
  (env'', leftover_bndrs, rule_bs, rule_es, bs', spec_args)
    <- specHeader env' bndrs args
  pure ( env''
       , leftover_bndrs
       , fst bndr' : rule_bs
       , bndrToCoreExpr (fst bndr') : rule_es
       , bndr' : bs'
       , bndrToCoreExpr (fst bndr') : spec_args
       )

specHeader env ((C.Id b, k@Just{}) : bndrs) (UnspecArg : args) = do
  let (env', bndr') = substLamBndr env (C.Id (zapIdOccInfo b), k)
  (env'', leftover_bndrs, rule_bs, rule_es, bs', spec_args)
    <- specHeader env' bndrs args

  let bndr_ty = case bndr' of
                  (C.Id b, _) -> varType b
                  _ -> panic "unreachable"

      (mb_spec_bndr, spec_arg)
        | isDeadBinder b
        , Just lit_expr <- panic "mkLitRubbish bndr_ty"
        = (Nothing, lit_expr)
        | otherwise
        = (Just bndr', bndrToCoreExpr (fst bndr'))

  pure ( env''
       , leftover_bndrs
       , fst bndr' : rule_bs
       , bndrToCoreExpr (fst bndr') : rule_es
       , case mb_spec_bndr of
           Just b' -> b' : bs'
           Nothing -> bs'
       , spec_arg : spec_args
       )

specHeader env [] _ = pure (env, [], [], [], [], [])
specHeader env bndrs [] = pure (env', bndrs', [], [], [], [])
  where
    (env', bndrs') = substLamBndrs env bndrs

specHeader _ bs args = pprPanic "specHeader mismatch" (vcat [ ppr bs, ppr args ])

{- *********************************************************************
*                                                                      *
            UsageDetails
*                                                                      *
********************************************************************* -}

data UsageDetails = MkUD
  { ud_calls :: !CallDetails }

emptyUDs :: UsageDetails
emptyUDs = MkUD { ud_calls = emptyDVarEnv }

type CallDetails = DVarEnv CoreId CallInfoSet

data CallInfoSet = CIS CoreId (Bag CallInfo)

data CallInfo = CI
  { ci_key :: [SpecArg]
  }

unionCalls :: CallDetails -> CallDetails -> CallDetails 
unionCalls c1 c2 = plusDVarEnv_C unionCallInfoSet c1 c2

unionCallInfoSet :: CallInfoSet -> CallInfoSet -> CallInfoSet
unionCallInfoSet (CIS f calls1) (CIS _ calls2) = CIS f (calls1 `unionBags` calls2)

singleCall :: SpecEnv -> CoreId -> [SpecArg] -> UsageDetails
singleCall spec_env id args = MkUD $ unitDVarEnv id $ CIS id $
                              unitBag (CI { ci_key = args })

mkCallUDs :: SpecEnv -> OutExpr -> [OutExpr] -> UsageDetails
mkCallUDs env fun args
  | (_, Var f) <- stripTicksTop tickishFloatable fun
  = mkCallUDs' env f args
  | otherwise
  = emptyUDs

mkCallUDs' :: SpecEnv -> CoreId -> [OutExpr] -> UsageDetails
mkCallUDs' env f args
  | not (null ci_key)
  = singleCall env f ci_key
  | otherwise
  = emptyUDs
  where
    pis = fst $ splitPiTys $ varType f

    ci_key :: [SpecArg]
    ci_key = dropWhileEndLE (not . isSpecUseful) $
             zipWith mk_spec_arg args pis

    -- TODO: we /could/ specialize higher order funcs here:
    -- add a data con 'SpecArg CoreExpr' to 'SpecArg'
    -- Here, under the AnonTy case, we can check if the type is
    -- a function, and then spec the argument.
    -- Need to be careful this happens late in pipeline,
    -- after inlining of no-work combinators.
    -- Maybe only do this when the arg is also just a 'Var x' (not for value lambdas?)
    -- Although, value lambdas may be floated by this point?
    mk_spec_arg :: OutExpr -> PiTyBinder Zk -> SpecArg
    mk_spec_arg (Type ty) (NamedTy _) = SpecType ty
    mk_spec_arg (KiCo _) (NamedKiCo _) = UnspecKiCo
    mk_spec_arg (Kind _) (NamedKi _) = UnspecKind
    mk_spec_arg _ (AnonTy _) = UnspecArg
    mk_spec_arg a b = pprPanic "ci_key" (ppr a $$ ppr b)

thenUDs :: UsageDetails -> UsageDetails -> UsageDetails
thenUDs (MkUD calls1) (MkUD calls2) = MkUD (calls1 `unionCalls` calls2)

dumpUDs :: [CoreBndr] -> UsageDetails -> UsageDetails
dumpUDs bndrs uds@MkUD{ ud_calls = orig_calls }
  | null bndrs = uds
  | otherwise = free_uds
  where
    free_uds = MkUD { ud_calls = free_calls }
    free_calls = deleteCallsFor bndrs orig_calls

dumpBindUDs :: [CoreId] -> UsageDetails -> UsageDetails -- The bool is always false
dumpBindUDs bndrs MkUD{ ud_calls = orig_calls }
  = free_uds
  where
    free_uds = MkUD { ud_calls = free_calls }
    free_calls = deleteCallsFor (C.Id <$> bndrs) orig_calls

callsForMe :: CoreId -> UsageDetails -> (UsageDetails, [CallInfo])
callsForMe fn uds@MkUD{ ud_calls = orig_calls }
  = (uds_without_me, calls_for_me)
  where
    uds_without_me = uds { ud_calls = delDVarEnv orig_calls fn }
    calls_for_me = case lookupDVarEnv orig_calls fn of
                     Nothing -> []
                     Just cis -> filterCalls cis

filterCalls :: CallInfoSet -> [CallInfo]
filterCalls (CIS fn call_bag)
  = de_dupd_calls
  where
    de_dupd_calls = remove_dups call_bag

remove_dups :: Bag CallInfo -> [CallInfo]
remove_dups calls = foldr add [] calls
  where
    add :: CallInfo -> [CallInfo] -> [CallInfo]
    add ci [] = [ci]
    add ci1 (ci2:cis) | ci2 `beats_or_same` ci1 = ci2:cis
                      | ci1 `beats_or_same` ci2 = ci1:cis
                      | otherwise = ci2 : add ci1 cis

beats_or_same :: CallInfo -> CallInfo -> Bool
beats_or_same CI{ ci_key = args1 } CI{ ci_key = args2 }
  = go args1 args2
  where
    go [] _ = True
    go (arg1 : args1) (arg2 : args2) = go_arg arg1 arg2 && go args1 args2
    go (_:_) [] = False

    go_arg (SpecType ty1) (SpecType ty2) = isJust (tcMatchTy ty1 ty2)
    go_arg UnspecType UnspecType = True
    go_arg UnspecKiCo UnspecKiCo = True
    go_arg UnspecKind UnspecKind = True
    go_arg UnspecArg UnspecArg = True
    go_arg _ _ = False

deleteCallsFor :: [CoreBndr] -> CallDetails -> CallDetails
deleteCallsFor bndrs calls =
  let bndrs' = mapMaybe runtimeVar_maybe bndrs
  in delDVarEnvList calls bndrs'

{- *********************************************************************
*                                                                      *
            Monad and helpers
*                                                                      *
********************************************************************* -}

type SpecM a = UniqSM a

runSpecM :: SpecM a -> CoreM a
runSpecM thing_inside = do
  us <- getUniqueSupplyM
  return (initUs_ us thing_inside)

mapAndCombineSM :: (a -> SpecM (b, UsageDetails)) -> [a] -> SpecM ([b], UsageDetails)
mapAndCombineSM _ [] = return ([], emptyUDs)
mapAndCombineSM f (x:xs) = do
  (y, uds1) <- f x
  (ys, uds2) <- mapAndCombineSM f xs
  return (y:ys, uds1 `thenUDs` uds2)

extendTvSubst :: SpecEnv -> CoreTyVar -> CoreType -> SpecEnv
extendTvSubst env tv ty
  = env { se_subst = Core.extendTvSubst (se_subst env) tv ty }

extendInScope :: SpecEnv -> OutId -> SpecEnv
extendInScope env@(SE { se_subst = subst }) bndr
  = env { se_subst = subst `Core.extendTermSubstInScope` C.Id bndr }

zapSubst :: SpecEnv -> SpecEnv
zapSubst env@SE{ se_subst = subst }
  = env { se_subst = Core.zapSubst subst }

substTy :: SpecEnv -> CoreType -> CoreType
substTy env ty = Core.substTyUnchecked (se_subst env) ty

substTyCo :: SpecEnv -> TypeCoercion Zk -> TypeCoercion Zk
substTyCo env co = panic "substTyCo"

substKiCo :: SpecEnv -> KindCoercion Zk -> KindCoercion Zk
substKiCo env co = Core.substKiCo (se_subst env) co

substKi :: SpecEnv -> CoreMonoKind -> CoreMonoKind
substKi env ki = Core.substMonoKiUnchecked (se_subst env) ki

substLamBndr
  :: SpecEnv
  -> (CoreBndr, Maybe CoreMonoKind)
  -> (SpecEnv, (CoreBndr, Maybe CoreMonoKind))
substLamBndr env b = case Core.substLamBndr (se_subst env) b of
                       (subst', b') -> (env { se_subst = subst' }, b')

substLamBndrs
  :: SpecEnv
  -> [(CoreBndr, Maybe CoreMonoKind)]
  -> (SpecEnv, [(CoreBndr, Maybe CoreMonoKind)])
substLamBndrs env bs = case Core.substLamBndrs (se_subst env) bs of
                         (subst', bs') -> (env { se_subst = subst' }, bs')

substLetBndrs :: SpecEnv -> [CoreId] -> (SpecEnv, [CoreId])
substLetBndrs env bs = case Core.substLetBndrs (se_subst env) bs of
                         (subst', bs') -> (env { se_subst = subst' }, bs')

substLetBndr :: SpecEnv -> CoreId -> (SpecEnv, CoreId)
substLetBndr env b = case Core.substLetBndr (se_subst env) b of
                       (subst', b') -> (env { se_subst = subst' }, b')

cloneLetBndrSM :: SpecEnv -> CoreId -> SpecM (SpecEnv, CoreId)
cloneLetBndrSM env@SE{ se_subst = subst } bndr = do
  (subst', bndr') <- Core.cloneIdBndr subst bndr
  return (env { se_subst = subst' }, bndr')

cloneRecBndrsSM :: SpecEnv -> [CoreId] -> SpecM (SpecEnv, [CoreId])
cloneRecBndrsSM env@SE{ se_subst = subst } bndrs = do
  (subst', bndrs') <- Core.cloneRecIdBndrs subst bndrs
  return (env { se_subst = subst' }, bndrs')

newSpecIdSM :: Name -> CoreType -> IdDetails -> IdInfo -> SpecM CoreId
newSpecIdSM old_name new_ty details info = do
  uniq <- getUniqueM
  let new_occ = mkSpecOcc (nameOccName old_name)
      new_name = mkInternalName uniq new_occ (getSrcSpan old_name)
  return $ assert (not (isTyCoVarType new_ty)) $
    mkLocalIdWithDetailsAndInfo details new_name new_ty info
