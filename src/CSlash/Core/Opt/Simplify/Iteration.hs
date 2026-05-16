{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Opt.Simplify.Iteration where

import CSlash.Driver.Flags

import CSlash.Core as C
import CSlash.Core.Opt.Simplify.Monad
import CSlash.Core.Opt.ConstantFold
import CSlash.Core.Subst (mkEmptyTermSubst, mkEmptyTermSubstIS)
import CSlash.Core.Type
import CSlash.Core.Type.Compare( eqType )
import CSlash.Core.Kind
import CSlash.Core.Opt.Simplify.Env
import CSlash.Core.Opt.Simplify.Inline
import CSlash.Core.Opt.Simplify.Utils
import CSlash.Core.Opt.OccurAnal
  ( occurAnalyzeExpr, zapLambdaBndrs, scrutOkForBinderSwap, BinderSwapDecision (..) )
import CSlash.Core.Make ( FloatBind, mkCoreLams, mkCoreApps{-, mkImpossibleExpr-}, castBottomExpr )
import qualified CSlash.Core.Make as Make
import CSlash.Core.Reduction
import CSlash.Core.Opt.Coercion ( optTyCoercion, optKiCoercion )
import CSlash.Core.DataCon
   ( DataCon, dataConId
--   , dataConRepArgTys, isUnboxedTupleDataCon
   )
import CSlash.Core.Opt.Stats ( Tick(..) )
import CSlash.Core.Ppr ( pprCoreExpr )
import CSlash.Core.Unfold
import CSlash.Core.Unfold.Make
import CSlash.Core.Utils
import CSlash.Core.Opt.Arity ( ArityType{-, exprArity-}, arityTypeBotSigs_maybe
                             {-, pushCoTyArg, pushCoValArg, exprIsDeadEnd-}
                             , typeArity, arityTypeArity, etaExpandAT )
import CSlash.Core.SimpleOpt
  ( exprIsConApp_maybe, joinPointBinding_maybe, joinPointBindings_maybe )
-- import CSlash.Core.FVs (mkRuleInfo)
import CSlash.Core.Rules (lookupRule, getRules)
-- import GHC.Types.Literal   ( litIsLifted ) --, mkLitInt ) -- temporarily commented out. See #8326
import CSlash.Types.SourceText
import CSlash.Types.Var
import CSlash.Types.Var.Id
-- import CSlash.Types.Id.Make   ( seqId )
import CSlash.Types.Var.Id.Info
import CSlash.Types.Name ( mkSystemVarName, isExternalName, getOccFS )
import CSlash.Types.Demand
import CSlash.Types.Unique ( hasKey )
import CSlash.Types.Unique.Supply
import CSlash.Types.Basic
import CSlash.Types.Tickish
-- import GHC.Builtin.Types.Prim( realWorldStatePrimTy )
-- import GHC.Builtin.Names( runRWKey, seqHashKey )

import CSlash.Data.Maybe ( isNothing, orElse, mapMaybe )
import CSlash.Data.FastString
import CSlash.Unit.Module ( moduleName )
import CSlash.Utils.Outputable
import CSlash.Utils.Trace
import CSlash.Utils.Panic
import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Monad  ( mapAccumLM, liftIO )
import CSlash.Utils.Logger
import CSlash.Utils.Misc

import Control.Monad

{- *********************************************************************
*                                                                      *
        Bindings
*                                                                      *
********************************************************************* -}

simplTopBinds :: SimplEnv -> [InBind] -> SimplM (SimplFloats, SimplEnv)
simplTopBinds env0 binds0 = do
  !env1 <- {-# SCC "simplTopBinds-simplRecBndrs" #-} simplRecBndrs env0 (bindersOfBinds binds0)

  (floats, env2) <- {-# SCC "simplTopBinds-simpl_binds" #-} simpl_binds env1 binds0
  freeTick SimplifierDone
  return (floats, env2)
  where
    simpl_binds :: SimplEnv -> [InBind] -> SimplM (SimplFloats, SimplEnv)
    simpl_binds env [] = return (emptyFloats env, env)
    simpl_binds env (bind:binds) = do
      (float, env1) <- simpl_bind env bind
      (floats, env2) <- simpl_binds env1 binds
      let !floats1 = float `addFloats` floats
      return (floats1, env2)

    simpl_bind env (Rec pairs) = simplRecBind env (BC_Let TopLevel Recursive) pairs
    simpl_bind env (NonRec b r) = do
      let bind_cxt = BC_Let TopLevel NonRecursive
      (env', b') <- addBndrRules env b (lookupRecBndr env b) bind_cxt
      simplRecOrTopPair env' bind_cxt b b' r

{- *********************************************************************
*                                                                      *
        Bindings
*                                                                      *
********************************************************************* -}

simplRecBind
  :: SimplEnv
  -> BindContext
  -> [(InId, InExpr)]
  -> SimplM (SimplFloats, SimplEnv)
simplRecBind env0 bind_cxt pairs0 = do
  (env1, triples) <- mapAccumLM add_rules env0 pairs0
  let new_bndrs = map sndOf3 triples
  (rec_floats, env2) <- enterRecGroupRHSs env1 new_bndrs $ \env -> go env triples
  return (mkRecFloats rec_floats, env2)
  where
    add_rules :: SimplEnv -> (InId, InExpr) -> SimplM (SimplEnv, (InId, OutId, InExpr))
    add_rules env (bndr, rhs) = do
      (env', bndr') <- addBndrRules env bndr (lookupRecBndr env bndr) bind_cxt
      return (env', (bndr, bndr', rhs))

    go env [] = return (emptyFloats env, env)
    go env ((old_bndr, new_bndr, rhs) : pairs) = do
      (float, env1) <- simplRecOrTopPair env bind_cxt old_bndr new_bndr rhs
      (floats, env2) <- go env1 pairs
      return (float `addFloats` floats, env2)

simplRecOrTopPair
  :: SimplEnv
  -> BindContext
  -> InId
  -> OutId
  -> InExpr
  -> SimplM (SimplFloats, SimplEnv)
simplRecOrTopPair env bind_cxt old_bndr new_bndr rhs
  | Just env' <- preInlineUnconditionally env (bindContextLevel bind_cxt) old_bndr rhs env
  = {-# SCC "simplRecOrTopPair-pre-inline-uncond" #-}
    simplTrace "SimplBindr:inline_uncond" (ppr old_bndr) $ do
      tick (PreInlineUnconditionally old_bndr)
      return (emptyFloats env, env')

  | otherwise
  = case bind_cxt of
      BC_Join is_rec cont -> simplTrace "SimplBind:join" (ppr old_bndr) $
                             simplJoinBind is_rec cont
                             (old_bndr, env) (new_bndr, env) (rhs, env)

      BC_Let top_lvl is_rec -> simplTrace "SimplBind:normal" (ppr old_bndr) $
                               simplBind top_lvl is_rec
                               (old_bndr, env) (new_bndr, env) (rhs, env)
 
simplTrace :: String -> SDoc -> SimplM a -> SimplM a
simplTrace herald doc thing_inside = do
  logger <- getLogger
  if logHasDumpFlag logger Opt_D_verbose_core2core
    then logTraceMsg logger herald doc thing_inside
    else thing_inside

simplBind
  :: TopLevelFlag
  -> RecFlag
  -> (InId, SimplEnv)
  -> (OutId, SimplEnv)
  -> (InExpr, SimplEnv)
  -> SimplM (SimplFloats, SimplEnv)
simplBind top_lvl is_rec (bndr, unf_se) (bndr1, env) (rhs, rhs_se)
  = assertPpr (not (isJoinId bndr)) (ppr bndr) $ do
  let !rhs_env = rhs_se `setInScopeFromE` env
      (tkcvs, body) = case collectNonValBinders rhs of
                      (bndrs, body)
                        | surely_not_lam body -> (bndrs, body)
                      _ -> ([], rhs)

      surely_not_lam Lam{} = False
      surely_not_lam (Tick t e)
        | not (tickishFloatable t) = surely_not_lam e
      surely_not_lam _ = True

  (body_env, tkcvs') <- {-# SCC "simplBinders" #-} simplBinders rhs_env tkcvs

  let rhs_cont = mkRhsStop (substTy body_env (exprType body)) is_rec (idDemandInfo bndr)

  (body_floats0, body0) <- {-# SCC "simplExprF" #-} simplExprF body_env body rhs_cont

  (body_floats2, body2) <- {-# SCC "prepareBinding" #-}
                           prepareBinding env top_lvl is_rec bndr1 body_floats0 body0

  (rhs_floats, body3)
    <- if isEmptyFloats body_floats2 || null tkcvs
       then {-# SCC "simplBind-simple-floating" #-} return (body_floats2, body2)
       else {-# SCC "simplBind-type-abstraction-first" #-}
            do (poly_binds, body3) <- abstractFloats (seUnfoldingOpts env) top_lvl
                                      (fst <$> tkcvs') body_floats2 body2
               let poly_floats = foldl' extendFloats (emptyFloats env) poly_binds
               return (poly_floats, body3)

  let env1 = env `setInScopeFromF` rhs_floats
  rhs' <- rebuildLam env tkcvs' body3 rhs_cont
  (bind_float, env2) <- completeBind (BC_Let top_lvl is_rec) (bndr, unf_se) (bndr1, rhs', env1)
  return (rhs_floats `addFloats` bind_float, env2)

simplJoinBind
  :: RecFlag
  -> SimplCont
  -> (InId, SimplEnv)
  -> (OutId, SimplEnv)
  -> (InExpr, SimplEnv)
  -> SimplM (SimplFloats, SimplEnv)
simplJoinBind is_rec cont (old_bndr, unf_se) (new_bndr, env) (rhs, rhs_se) = do
  let rhs_env = rhs_se `setInScopeFromE` env
  rhs' <- simplJoinRhs rhs_env old_bndr rhs cont
  completeBind (BC_Join is_rec cont) (old_bndr, unf_se) (new_bndr, rhs', env)

simplAuxBind
  :: String
  -> SimplEnv
  -> InId
  -> OutExpr
  -> SimplM (SimplFloats, SimplEnv)
simplAuxBind _ env bndr new_rhs
  | assertPpr (not (isJoinId bndr)) (ppr bndr) $
    isDeadBinder bndr
  = return (emptyFloats env, env)

  | exprIsTrivial new_rhs
    || case (idOccInfo bndr) of
         OneOcc { occ_n_br = 1, occ_in_lam = NotInsideLam } -> True
         _ -> False
  = return (emptyFloats env, extendIdSubst env bndr (DoneEx new_rhs NotJoinPoint))

  | otherwise
  = do let !occ_fs = getOccFS bndr
       (anf_floats, rhs1) <- prepareRhs env NotTopLevel occ_fs new_rhs
       unless (isEmptyLetFloats anf_floats) (tick LetFloatFromLet)
       let rhs_floats = emptyFloats env `addLetFloats` anf_floats

       (env1, new_bndr) <- simplIdBinder (env `setInScopeFromF` rhs_floats) bndr
       (bind_float, env2) <- completeBind (BC_Let NotTopLevel NonRecursive)
                             (bndr, env) (new_bndr, rhs1, env1)

       return (rhs_floats `addFloats` bind_float, env2)

{- *********************************************************************
*                                                                      *
           trySimplCast
*                                                                      *
********************************************************************* -}

trySimplCast
  :: SimplEnv
  -> BindContext
  -> InId
  -> OutId
  -> OutExpr
  -> SimplM (SimplFloats, SimplEnv)
trySimplCast env bind_cxt old_bndr bndr (Cast rhs co)
  | BC_Let top_lvl is_rec <- bind_cxt
  , not (exprIsTrivial rhs)
  , not (hasInlineUnfolding info)
  , not (isOpaquePragma (idInlinePragma old_bndr))
  = do uniq <- getUniqueM
       let work_name = mkSystemVarName uniq occ_fs
           work_id = mkLocalIdWithInfo work_name work_ty work_info

       (rhs_floats, work_rhs) <- prepareBinding env top_lvl is_rec work_id (emptyFloats env) rhs

       work_unf <- mk_worker_unfolding top_lvl work_id work_rhs
       let work_id_w_unf = work_id `setIdUnfolding` work_unf
           floats = rhs_floats `addLetFloats`
                    unitLetFloat (NonRec work_id_w_unf work_rhs)

           triv_rhs = Cast (Var work_id_w_unf) co

       if postInlineUnconditionally env bind_cxt old_bndr bndr triv_rhs
         then do tick (PostInlineUnconditionally bndr)
                 return ( floats
                        , extendIdSubst (setInScopeFromF env floats) old_bndr $
                          DoneEx triv_rhs NotJoinPoint )
         else do wrap_unf <- mkLetUnfolding env top_lvl VanillaSrc bndr False triv_rhs
                 let bndr' = bndr `setInlinePragma` mkCastWrapperInlinePrag
                                                    (idInlinePragma bndr)
                                  `setIdUnfolding` wrap_unf
                     floats' = floats `extendFloats` NonRec bndr' triv_rhs
                 return (floats', setInScopeFromF env floats')
  where
    !occ_fs = getOccFS bndr
    work_ty = tycoercionLType co
    info = idInfo bndr
    work_arity = arityInfo info `min` typeArity work_ty

    mk_worker_unfolding top_lvl work_id work_rhs
      = case realUnfoldingInfo info of
      unf@CoreUnfolding{ uf_tmpl = unf_rhs, uf_src = src }
        | isStableSource src -> return (unf { uf_tmpl = mkCast unf_rhs (mkSymTyCo co) })
      _ -> mkLetUnfolding env top_lvl VanillaSrc work_id False work_rhs

    work_info = vanillaIdInfo `setDmdSigInfo` dmdSigInfo info
                              `setDemandInfo` demandInfo info
                              `setInlinePragInfo` inlinePragInfo info
                              `setArityInfo` work_arity

trySimplCast env _ _ bndr rhs = do
  traceSmpl "trySimplCast:no"
    $ vcat [ text "bndr:" <+> ppr bndr
           , text "rhs:" <+> ppr rhs ]
  return (mkFloatBind env (NonRec bndr rhs))
         
mkCastWrapperInlinePrag :: InlinePragma -> InlinePragma
mkCastWrapperInlinePrag InlinePragma{ inl_inline = fn_inl, inl_act = fn_act, inl_rule = rule_info }
  = InlinePragma { inl_src = SourceText $ fsLit "{-# INLINE"
                 , inl_inline = fn_inl
                 , inl_sat = Nothing
                 , inl_act = wrap_act
                 , inl_rule = rule_info }
  where
    wrap_act | isNeverActive fn_act = activateDuringFinal
             | otherwise = fn_act

{- *********************************************************************
*                                                                      *
           prepareBinding, prepareRhs, makeTrivial
*                                                                      *
********************************************************************* -}

prepareBinding
  :: SimplEnv
  -> TopLevelFlag
  -> RecFlag
  -> CoreId
  -> SimplFloats
  -> OutExpr
  -> SimplM (SimplFloats, OutExpr)
prepareBinding env top_lvl is_rec bndr rhs_floats rhs = do
  let (rhs_floats1, rhs1) = wrapJoinFloatsX rhs_floats rhs

      rhs_env = env `setInScopeFromF` rhs_floats1
      !occ_fs = getOccFS bndr

  (anf_floats, rhs2) <- prepareRhs rhs_env top_lvl occ_fs rhs1

  let all_floats = rhs_floats1 `addLetFloats` anf_floats

  if doFloatFromRhs (seFloatEnable env) top_lvl is_rec all_floats rhs2
    then do tick LetFloatFromLet
            return (all_floats, rhs2)
    else return (emptyFloats env, wrapFloats rhs_floats1 rhs1)

prepareRhs
  :: HasDebugCallStack
  => SimplEnv
  -> TopLevelFlag
  -> FastString
  -> OutExpr
  -> SimplM (LetFloats, OutExpr)
prepareRhs env top_lvl occ rhs0
  | is_expandable = anfise rhs0
  | otherwise = return (emptyLetFloats, rhs0)
  where
    is_expandable = go rhs0 0
      where
        go (Var fun) n_val_args = isExpandableApp fun n_val_args
        go (App fun arg) n_val_args
          | isNonValArg arg = go fun n_val_args
          | otherwise = go fun (n_val_args + 1)
        go (Cast rhs _) n_val_args = go rhs n_val_args
        go (Tick _ rhs) n_val_args = go rhs n_val_args
        go _ _ = False

    anfise :: OutExpr -> SimplM (LetFloats, OutExpr)
    anfise (Cast rhs co) = do
      (floats, rhs') <- anfise rhs
      return (floats, Cast rhs' co)
    anfise (App fun (Type ty)) = do
      (floats, rhs') <- anfise fun
      return (floats, App rhs' (Type ty))
    anfise (App fun (KiCo co)) = do
      (floats, rhs') <- anfise fun
      return (floats, App rhs' (KiCo co))
    anfise (App fun (Kind ki)) = do
      (floats, rhs') <- anfise fun
      return (floats, App rhs' (Kind ki))
    anfise (App fun arg) = do
      (floats1, fun') <- anfise fun
      (floats2, arg') <- makeTrivial env top_lvl topDmd occ arg
      return (floats1 `addLetFlts` floats2, App fun' arg')
    anfise (Var fun) = return (emptyLetFloats, Var fun)
    anfise (Tick t rhs)
      | tickishScoped t == NoScope
      = do (floats, rhs') <- anfise rhs
           return (floats, Tick t rhs')

      | (not (tickishCounts t) || tickishCanSplit t)
      = do (floats, rhs') <- anfise rhs
           let tickIt (id, expr) = (id, mkTick (mkNoCount t) expr)
               floats' = mapLetFloats floats tickIt
           return (floats', Tick t rhs')

    anfise other = return (emptyLetFloats, other)

makeTrivialArg :: HasDebugCallStack => SimplEnv -> ArgSpec -> SimplM (LetFloats, ArgSpec)
makeTrivialArg env arg@ValArg{ as_arg = e, as_dmd = dmd } = do
  (floats, e') <- makeTrivial env NotTopLevel dmd (fsLit "arg") e
  return (floats, arg { as_arg = e })

makeTrivialArg _ arg = return (emptyLetFloats, arg)

makeTrivial
  :: HasDebugCallStack
  => SimplEnv
  -> TopLevelFlag
  -> Demand
  -> FastString
  -> OutExpr
  -> SimplM (LetFloats, OutExpr)
makeTrivial env top_lvl dmd occ_fs expr
  | exprIsTrivial expr
    || not (bindingOk top_lvl expr expr_ty)
  = return (emptyLetFloats, expr)

  | Cast expr' co <- expr
  = do (floats, triv_expr) <- makeTrivial env top_lvl dmd occ_fs expr'
       return (floats, Cast triv_expr co)

  | otherwise
  = do (floats, expr1) <- prepareRhs env top_lvl occ_fs expr
       uniq <- getUniqueM
       let name = mkSystemVarName uniq occ_fs
           var = mkLocalIdWithInfo name expr_ty id_info

       (arity_type, expr2) <- tryEtaExpandRhs env (BC_Let top_lvl NonRecursive) var expr1

       unf <- mkLetUnfolding env top_lvl VanillaSrc var False expr2

       let final_id = addLetBndrInfo var arity_type unf
           bind = NonRec final_id expr2

       traceSmpl "makeTrivial"
         $ vcat [ text"final_id" <+> ppr final_id
                , text "rhs" <+> ppr expr2 ]

       return (floats `addLetFlts` unitLetFloat bind, Var final_id)
  where
    id_info = vanillaIdInfo `setDemandInfo` dmd
    expr_ty = exprType expr

bindingOk :: TopLevelFlag -> CoreExpr -> CoreType -> Bool
bindingOk top_lvl expr expr_ty
  | isTopLevel top_lvl = exprIsTopLevelBindable expr expr_ty
  | otherwise = True

{- *********************************************************************
*                                                                      *
           Completing a binding
*                                                                      *
********************************************************************* -}

completeBind
  :: BindContext
  -> (InId, SimplEnv)
  -> (OutId, OutExpr, SimplEnv)
  -> SimplM (SimplFloats, SimplEnv)
completeBind bind_cxt (old_bndr, unf_se) (new_bndr, new_rhs, env) = do
  let old_info = idInfo old_bndr
      old_unf = realUnfoldingInfo old_info

  (new_arity, eta_rhs) <- tryEtaExpandRhs env bind_cxt new_bndr new_rhs

  new_unfolding <- simplLetUnfolding (unf_se `setInScopeFromE` env)
                   bind_cxt old_bndr
                   eta_rhs (varType new_bndr)
                   new_arity old_unf

  let new_bndr_w_info = addLetBndrInfo new_bndr new_arity new_unfolding

  if postInlineUnconditionally env bind_cxt old_bndr new_bndr_w_info eta_rhs
    then do tick (PostInlineUnconditionally old_bndr)
            let unf_rhs = maybeUnfoldingTemplate new_unfolding `orElse` eta_rhs

            simplTrace "PostInlineUnconditionally" (ppr new_bndr <+> ppr unf_rhs) $
              return ( emptyFloats env
                     , extendIdSubst env old_bndr $
                       DoneEx unf_rhs (idJoinPointHood new_bndr) )
    else trySimplCast env bind_cxt old_bndr new_bndr_w_info eta_rhs

addLetBndrInfo :: OutId -> ArityType -> Unfolding -> OutId
addLetBndrInfo new_bndr new_arity_type new_unf
  = new_bndr `setIdInfo` info5
  where
    new_arity = arityTypeArity new_arity_type
    info1 = idInfo new_bndr `setArityInfo` new_arity

    info2 = info1 `setUnfoldingInfo` new_unf

    info3 = info2

    info4 = case arityTypeBotSigs_maybe new_arity_type of
      Nothing -> info3
      Just (ar, dmd_sig) -> assert (ar == new_arity) $
                            info3 `setDmdSigInfo` dmd_sig

    info5 = zapCallArityInfo info4


{- *********************************************************************
*                                                                      *
           simpleExpr
*                                                                      *
********************************************************************* -}

simplExpr :: SimplEnv -> CoreExpr -> SimplM CoreExpr 
simplExpr !env (Type ty) = do
  ty' <- simplType env ty
  return (Type ty')
simplExpr !env (Kind ki) = do
  ki' <- simplKind env ki
  return (Kind ki')

simplExpr env expr = simplExprC env expr (mkBoringStop expr_out_ty)
  where
    expr_out_ty = substTy env (exprType expr)

simplExprC
  :: SimplEnv
  -> InExpr
  -> SimplCont
  -> SimplM OutExpr
simplExprC env expr cont = do
  (floats, expr') <- simplExprF env expr cont
  return (wrapFloats floats expr')

simplExprF
  :: SimplEnv
  -> InExpr
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)
simplExprF !env e !cont = simplExprF1 env e cont

simplExprF1
  :: HasDebugCallStack
  => SimplEnv
  -> InExpr
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)
simplExprF1 _ (Type ty) cont = pprPanic "simplExprF: type" (ppr ty <+> text "cont:" <+> ppr cont)
simplExprF1 _ (Kind ki) cont = pprPanic "simplExprF: kind" (ppr ki <+> text "cont:" <+> ppr cont)

simplExprF1 env (Var v) cont = {-# SCC "simplIdF" #-} simplIdF env v cont
simplExprF1 env (Lit lit) cont = {-# SCC "rebuild" #-} rebuild env (Lit lit) cont
simplExprF1 env (Tick t expr) cont = {-# SCC "simplTick" #-} simplTick env t expr cont
simplExprF1 env (Cast body co) cont = {-# SCC "simplCast" #-} simplCast env body co cont
simplExprF1 env (KiCo co) cont = {-# SCC "simplKiCoF" #-} simplKiCoF env co cont

simplExprF1 env (App fun arg) cont
  = {-# SCC "simplExprF1-App" #-}
  case arg of
    Type ty -> do arg' <- simplType env ty
                  let hole' = substTy env (exprType fun)
                  simplExprF env fun $
                    ApplyToTy { sc_arg_ty = arg'
                              , sc_hole_ty = hole'
                              , sc_cont = cont }
    KiCo co -> panic "simplExprF1 App KiCo"
    Kind ki -> do arg' <- simplKind env ki
                  let hole' = substTy env (exprType fun)
                  simplExprF env fun $
                    ApplyToKi { sc_arg_ki = arg'
                              , sc_hole_ty = hole'
                              , sc_cont = cont }
    _ -> simplExprF env fun $
         ApplyToVal { sc_arg = arg
                    , sc_env = env
                    , sc_hole_ty = substTy env (exprType fun)
                    , sc_dup = NoDup
                    , sc_cont = cont }

simplExprF1 env expr@Lam{} cont
  = {-# SCC "simplExprF1-Lam" #-}
    simplLam env (zapLambdaBndrs expr n_args) cont
  where n_args = countArgs cont

simplExprF1 env (Case scrut bndr _ alts) cont
  = {-# SCC "simplExprF1-Case" #-}
    simplExprF env scrut (Select { sc_dup = NoDup
                                 , sc_bndr = bndr
                                 , sc_alts = alts
                                 , sc_env = env
                                 , sc_cont = cont })

simplExprF1 env (Let (Rec pairs) body) cont
  | Just pairs' <- joinPointBindings_maybe pairs
  = {-# SCC "simplRecJoinPoint" #-} simplRecJoinPoint env pairs' body cont

  | otherwise
  = {-# SCC "simplRecE" #-} simplRecE env pairs body cont

simplExprF1 env (Let (NonRec bndr rhs) body) cont
  | Type ty <- rhs
  = pprPanic "simplExprF1 type let" (text "let" <+> ppr bndr <+> text "=" <+> ppr ty)
  | Kind ki <- rhs
  = pprPanic "simplExprF1 kind let" (text "let" <+> ppr bndr <+> text "=" <+> ppr ki)
  | KiCo co <- rhs
  = pprPanic "simplExprF1 kico let" (text "let" <+> ppr bndr <+> text "=" <+> ppr co)

  | Just env' <- preInlineUnconditionally env NotTopLevel bndr rhs env
  = do tick (PreInlineUnconditionally bndr)
       simplExprF env' body cont

  | Just (bndr', rhs') <- joinPointBinding_maybe bndr rhs
  = {-# SCC "simplNonRecJoinPoint" #-}
    simplNonRecJoinPoint env bndr' rhs' body cont
  | otherwise
  = {-# SCC "simplNonRecE" #-}
    simplNonRecE env FromLet bndr (rhs, env) body cont

simplJoinRhs
  :: SimplEnv
  -> InId
  -> InExpr
  -> SimplCont
  -> SimplM OutExpr
simplJoinRhs env bndr expr cont
  | JoinPoint arity <- idJoinPointHood bndr
  = do let (join_bndrs, join_body) = collectNBinders arity expr
       (env', join_bndrs') <- simplLamBndrs env join_bndrs
       join_body' <- simplExprC env' join_body cont
       return $ mkCoreLams join_bndrs' join_body'
  | otherwise
  = pprPanic "simplJoinRhs" (ppr bndr)

simplType :: SimplEnv -> InType -> SimplM OutType
simplType env ty = seqType new_ty `seq` return new_ty
  where new_ty = substTy env ty

simplKind :: SimplEnv -> InMonoKind -> SimplM OutMonoKind
simplKind env ki = seqMonoKind new_ki `seq` return new_ki
  where new_ki = substMonoKi env ki

simplKiCoF
  :: SimplEnv
  -> InKindCoercion
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)
simplKiCoF env co cont = do
  co' <- simplKiCo env co
  rebuild env (KiCo co') cont

simplKiCo :: SimplEnv -> InKindCoercion -> SimplM OutKindCoercion
simplKiCo env co = do
  let opt_co | reSimplifying env = substKiCo env co
             | otherwise = optKiCoercion opts subst co
  seqKiCo opt_co `seq` return opt_co
  where
    subst = getSubst env
    opts = seOptCoercionOpts env

simplTyCo :: SimplEnv -> InTypeCoercion -> SimplM OutTypeCoercion
simplTyCo env co = do
  let opt_co | reSimplifying env = substTyCo env co
             | otherwise = optTyCoercion opts subst co
  seqTyCo opt_co `seq` return opt_co
  where
    subst = getSubst env
    opts = seOptCoercionOpts env

simplTick
  :: SimplEnv
  -> CoreTickish
  -> InExpr
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)
simplTick env tickish expr cont
  | tickish `tickishScopesLike` SoftScope
  = do (floats, expr') <- simplExprF env expr cont
       return (floats, mkTick tickish expr')

  | Select{} <- cont, Just expr' <- push_tick_inside
  = simplExprF env expr' cont

  | otherwise
  = no_floating_past_tick
  where
    push_tick_inside = case expr0 of
      Case scrut bndr ty alts -> Just $ Case (tickScrut scrut) bndr ty (map tickAlt alts)
      _ -> Nothing
      where
        (ticks, expr0) = stripTicksTop movable (Tick tickish expr)
        movable t = not (tickishCounts t) ||
                    t `tickishScopesLike` NoScope ||
                    tickishCanSplit t
        tickScrut e = foldr mkTick e ticks
        tickAlt (Alt c bs e) = Alt c bs (foldr mkTick e ts_scope)
        ts_scope = map mkNoCount $ filter (not . (`tickishScopesLike` NoScope)) ticks

    no_floating_past_tick = do
      let (inc, outc) = splitCont cont
      (floats, expr1) <- simplExprF env expr inc
      let expr2 = wrapFloats floats expr1
          tickish' = simplTickish env tickish
      rebuild env (mkTick tickish' expr2) outc

    simplTickish env tickish@CpcTick{} = tickish

    splitCont :: SimplCont -> (SimplCont, SimplCont)
    splitCont cont@ApplyToTy{ sc_cont = tail } = (cont { sc_cont = inc }, outc)
      where (inc, outc) = splitCont tail
    splitCont cont@ApplyToKiCo{ sc_cont = tail } = (cont { sc_cont = inc }, outc)
      where (inc, outc) = splitCont tail
    splitCont cont@ApplyToKi{ sc_cont = tail } = (cont { sc_cont = inc }, outc)
      where (inc, outc) = splitCont tail
    splitCont cont@CastIt{ sc_cont = tail } = (cont { sc_cont = inc }, outc)
      where (inc, outc) = splitCont tail
    splitCont other = (mkBoringStop (contHoleType other), other)

    getDoneId (DoneId id) = Just id
    getDoneId (DoneEx (Var id) _) = Just id
    getDoneId (DoneEx e _) = getIdFromTrivialExpr_maybe e
    getDoneId other = pprPanic "getDoneId" (ppr other)


{- *********************************************************************
*                                                                      *
           The main rebuilder
*                                                                      *
********************************************************************* -}

rebuild :: SimplEnv -> OutExpr -> SimplCont -> SimplM (SimplFloats, OutExpr)
rebuild env expr cont = case cont of
  Stop {} -> return (emptyFloats env, expr)
  TickIt t cont -> rebuild env (mkTick t expr) cont
  CastIt { sc_co = co, sc_opt = opt, sc_cont = cont }
    -> rebuild env (mkCast expr co') cont
    where co' = optOutTyCoercion env co opt
  Select { sc_bndr = bndr, sc_alts = alts, sc_env = se, sc_cont = cont }
    -> rebuildCase (se `setInScopeFromE` env) expr bndr alts cont
  StrictArg { sc_fun = fun, sc_cont = cont, sc_fun_ty = fun_ty }
    -> rebuildCall env (addValArgTo fun expr fun_ty) cont
  StrictBind { sc_bndr = b, sc_body = body, sc_env = se, sc_cont = cont, sc_from = from_what }
    -> completeBindX (se `setInScopeFromE` env) from_what b expr body cont
  ApplyToTy { sc_arg_ty = ty, sc_cont = cont }
    -> rebuild env (App expr (Type ty)) cont
  ApplyToKiCo { sc_arg_kico = co, sc_cont = cont }
    -> rebuild env (App expr (KiCo co)) cont
  ApplyToKi { sc_arg_ki = ki, sc_cont = cont }
    -> rebuild env (App expr (Kind ki)) cont
  ApplyToVal { sc_arg = arg, sc_env = se, sc_dup = dup_flag, sc_cont = cont, sc_hole_ty = fun_ty }
    -> do (_, _, arg') <- simplArg env dup_flag fun_ty Nothing se arg
          rebuild env (App expr arg') cont

completeBindX
  :: SimplEnv
  -> FromWhat
  -> InId
  -> OutExpr
  -> InExpr
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)
completeBindX env from_what bndr rhs body cont
  | FromBeta <- from_what
  , needsCaseBinding rhs
  = do (env1, bndr1) <- simplNonRecBndr env bndr
       (floats, expr') <- simplNonRecBody env1 from_what body cont
       let expr'' = wrapFloats floats expr'
           case_expr = Case rhs bndr1 (contResultType cont) [Alt DEFAULT [] expr'']
       return (emptyFloats env, case_expr)

  | otherwise
  = do (env1, bndr1) <- simplNonRecBndr env bndr
       (env2, bndr2) <- addBndrRules env1 bndr bndr1 (BC_Let NotTopLevel NonRecursive)
       (rhs_floats, rhs1) <- prepareBinding env NotTopLevel NonRecursive
                             bndr2 (emptyFloats env) rhs
       let env3 = env2 `setInScopeFromF` rhs_floats
       (bind_float, env4) <- completeBind (BC_Let NotTopLevel NonRecursive)
                                          (bndr, env)
                                          (bndr2, rhs1, env3)
       (body_floats, body') <- simplNonRecBody env4 from_what body cont
       let all_floats = rhs_floats `addFloats` bind_float `addFloats` body_floats
       return (all_floats, body')


{- *********************************************************************
*                                                                      *
           Lambdas
*                                                                      *
********************************************************************* -}

optOutTyCoercion :: SimplEnv -> OutTypeCoercion -> Bool -> OutTypeCoercion
optOutTyCoercion env co already_optimized
  | already_optimized = co
  | otherwise = optTyCoercion opts empty_subst co
  where
    empty_subst = mkEmptyTermSubstIS (seInScope env)
    opts = seOptCoercionOpts env

simplCast
  :: SimplEnv
  -> InExpr
  -> InTypeCoercion
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)
simplCast env body co0 cont0 = do
  co1 <- {-# SCC "simpleCast-simplCoercion" #-} simplTyCo env co0
  cont1 <- {-# SCC "simplCast-addCoerce" #-}
    if isReflTyCo co1
    then return cont0
    else addCoerce co1 True cont0
  {-# SCC "simplCast-simplExprF" #-} simplExprF env body cont1
  where
    addCoerce :: OutTypeCoercion -> Bool -> SimplCont -> SimplM SimplCont
    addCoerce = panic "addCoerce"

simplArg
  :: SimplEnv
  -> DupFlag
  -> OutType
  -> Maybe ArgInfo
  -> StaticEnv
  -> CoreExpr
  -> SimplM (DupFlag, StaticEnv, OutExpr)
simplArg env dup_flag fun_ty mb_arg_info arg_env arg
  | isSimplified dup_flag
  = return (dup_flag, arg_env, arg)
  | otherwise
  = do let arg_env' = arg_env `setInScopeFromE` env
           arg_ty = funArgTy fun_ty
           stop = case mb_arg_info of
                    Nothing -> mkBoringStop arg_ty
                    Just ai -> mkStrictArgStop arg_ty ai
       arg' <- simplExprC arg_env' arg stop
       return (Simplified, zapSubstEnv arg_env', arg')


{- *********************************************************************
*                                                                      *
           Lambdas
*                                                                      *
********************************************************************* -}

simplNonRecBody
  :: SimplEnv
  -> FromWhat
  -> InExpr
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)
simplNonRecBody env from_what body cont
  = case from_what of
      FromLet -> simplExprF env body cont
      FromBeta -> simplLam env body cont

simplLam
  :: SimplEnv
  -> InExpr
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)
simplLam env (Lam bndr ki body) cont = simpl_lam env bndr ki body cont
simplLam env expr cont = simplExprF env expr cont

simpl_lam
  :: HasDebugCallStack
  => SimplEnv
  -> InBndr -> Maybe InMonoKind -> InExpr
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)

-- Type beta-reduction
simpl_lam env bndr ki body ApplyToTy{ sc_arg_ty = arg_ty, sc_cont = cont }
  | Tv tv <- bndr
  = do tick (BetaReduction bndr ki)
       simplLam (extendTvSubst env tv arg_ty) body cont
  | otherwise
  = panic "simpl_lam mismatch"

-- Coercion beta-reduction
-- TODO: do I need an sc_env here to subst the KiCo??
simpl_lam env bndr ki body ApplyToKiCo{ sc_arg_kico = arg_kico, sc_cont = cont }
  | KCv kcv <- bndr
  = do tick (BetaReduction bndr ki)
       simplLam (extendKCvSubst env kcv arg_kico) body cont
  | otherwise
  = panic "simpl_lam mismatch"

-- Value beta-reduction
simpl_lam env bndr ki body ApplyToVal{ sc_arg = arg, sc_env = arg_se
                                            , sc_cont = cont, sc_dup = dup
                                            , sc_hole_ty = fun_ty }
  | C.Id id <- bndr
  = do tick (BetaReduction bndr ki)
       let from_what = FromBeta
       if | isSimplified dup
            -> completeBindX env from_what id arg body cont
          | Just env' <- preInlineUnconditionally env NotTopLevel id arg arg_se
          , not (needsCaseBinding arg)
            -> do tick (PreInlineUnconditionally id)
                  simplLam env' body cont
          | otherwise
            -> simplNonRecE env from_what id (arg, arg_se) body cont
  | otherwise
  = panic "simpl_lam mismatch"

-- Discard a non-counting tick
simpl_lam env bndr ki body (TickIt tickish cont)
  | not (tickishCounts tickish)
  = simpl_lam env bndr ki body cont

-- Not enough args
simpl_lam env bndr ki body cont
  = do let (inner_bndrs, inner_body) = collectBinders body
       (env', bndrs') <- simplLamBndrs env ((bndr, ki):inner_bndrs)
       body' <- simplExpr env' inner_body
       new_lam <- rebuildLam env' bndrs' body' cont
       rebuild env' new_lam cont

simplLamBndr
  :: SimplEnv
  -> (InBndr, Maybe InMonoKind)
  -> SimplM (SimplEnv, (OutBndr, Maybe OutMonoKind))
simplLamBndr env (bndr, ki) = simplBinder env (zapBndrUnfolding bndr, ki)

simplLamBndrs
  :: SimplEnv
  -> [(InBndr, Maybe InMonoKind)]
  -> SimplM (SimplEnv, [(OutBndr, Maybe OutMonoKind)])
simplLamBndrs env bndrs = mapAccumLM simplLamBndr env bndrs

simplNonRecE
  :: HasDebugCallStack
  => SimplEnv
  -> FromWhat
  -> InId
  -> (InExpr, SimplEnv)
  -> InExpr
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)
simplNonRecE env from_what bndr (rhs, rhs_se) body cont
  | assert (not (isJoinId bndr)) $
    is_strict_bind
  = simplExprF (rhs_se `setInScopeFromE` env) rhs
               (StrictBind { sc_bndr = bndr, sc_body = body, sc_from = from_what
                           , sc_env = env, sc_cont = cont, sc_dup = NoDup })
  | otherwise
  = do (env1, bndr1) <- simplNonRecBndr env bndr
       (env2, bndr2) <- addBndrRules env1 bndr bndr1 (BC_Let NotTopLevel NonRecursive)
       (floats1, env3) <- simplBind NotTopLevel NonRecursive
                          (bndr, env) (bndr2, env2) (rhs, rhs_se)
       (floats2, expr') <- simplNonRecBody env3 from_what body cont
       return (floats1 `addFloats` floats2, expr')
  where
    is_strict_bind = case from_what of
      FromBeta -> True
      FromLet -> seCaseCase env
         
simplRecE
  :: SimplEnv
  -> [(InId, InExpr)]
  -> InExpr
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)
simplRecE env pairs body cont = do
  let bndrs = map fst pairs
  massert (all (not . isJoinId) bndrs)
  env1 <- simplRecBndrs env bndrs
  (floats1, env2) <- simplRecBind env1 (BC_Let NotTopLevel Recursive) pairs
  (floats2, expr') <- simplExprF env2 body cont
  return (floats1 `addFloats` floats2, expr')

{- *********************************************************************
*                                                                      *
                     Join points
*                                                                      *
********************************************************************* -}

simplNonRecJoinPoint
  :: SimplEnv
  -> InId
  -> InExpr
  -> InExpr
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)
simplNonRecJoinPoint env bndr rhs body cont
  = assert (isJoinId bndr) $
    wrapJoinCont env cont $ \env cont -> do
      let res_ty = contResultType cont
      (env1, bndr1) <- simplNonRecJoinBndr env bndr res_ty
      (env2, bndr2) <- addBndrRules env1 bndr bndr1 (BC_Join NonRecursive cont)
      (floats1, env3) <- simplJoinBind NonRecursive cont (bndr, env) (bndr2, env2) (rhs, env)
      (floats2, body') <- simplExprF env3 body cont
      return (floats1 `addFloats` floats2, body')

simplRecJoinPoint
  :: SimplEnv
  -> [(InId, InExpr)]
  -> InExpr
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)
simplRecJoinPoint env pairs body cont
  = wrapJoinCont env cont $ \env cont -> do
      let bndrs = map fst pairs
          res_ty = contResultType cont
      env1 <- simplRecJoinBndrs env bndrs res_ty
      (floats1, env2) <- simplRecBind env1 (BC_Join Recursive cont) pairs
      (floats2, body') <- simplExprF env2 body cont
      return (floats1 `addFloats` floats2, body')

wrapJoinCont
  :: SimplEnv
  -> SimplCont
  -> (SimplEnv -> SimplCont -> SimplM (SimplFloats, OutExpr))
  -> SimplM (SimplFloats, OutExpr)
wrapJoinCont env cont thing_inside
  | contIsStop cont
  = thing_inside env cont
  | not (seCaseCase env)
  = do (floats1, expr1) <- thing_inside env (mkBoringStop (contHoleType cont))
       let (floats2, expr2) = wrapJoinFloatsX floats1 expr1
       (floats3, expr3) <- rebuild (env `setInScopeFromF` floats2) expr2 cont
       return (floats2 `addFloats` floats3, expr3)
  | otherwise
  = do (floats1, cont') <- mkDupableCont env cont
       (floats2, result) <- thing_inside (env `setInScopeFromF` floats1) cont'
       return (floats1 `addFloats` floats2, result)

trimJoinCont :: CoreId -> JoinPointHood -> SimplCont -> SimplCont
trimJoinCont _ NotJoinPoint cont = cont
trimJoinCont var (JoinPoint arity) cont = trim arity cont
  where
    trim 0 cont@Stop{} = cont
    trim 0 cont = mkBoringStop (contResultType cont)
    trim n cont@ApplyToVal{ sc_cont = k } = cont { sc_cont = trim (n - 1) k }
    trim n cont@ApplyToTy{ sc_cont = k } = cont { sc_cont = trim (n - 1) k }
    trim n cont@ApplyToKiCo{ sc_cont = k } = cont { sc_cont = trim (n - 1) k }
    trim n cont@ApplyToKi{ sc_cont = k } = cont { sc_cont = trim (n - 1) k }
    trim _ cont = pprPanic "completeCall" $ ppr var $$ ppr cont

{- *********************************************************************
*                                                                      *
                     Variables
*                                                                      *
********************************************************************* -}

simplVar :: SimplEnv -> InId -> SimplM OutExpr
simplVar env var
  = case substId env var of
      ContEx ids tcvs tvs kcvs kvs e -> let env' = setSubstEnv env ids tcvs tvs kcvs kvs
                                        in simplExpr env' e
      DoneId var1 -> return (Var var1)
      DoneEx e _ -> return e

simplIdF :: SimplEnv -> InId -> SimplCont -> SimplM (SimplFloats, OutExpr)
simplIdF env var cont
  | isDataConId var
  = rebuild env (Var var) cont
  | otherwise
  = case substId env var of
      ContEx ids tcvs tvs kcvs kvs e -> simplExprF env' e cont
        where
          env' = setSubstEnv env ids tcvs tvs kcvs kvs

      DoneId var1 -> do
        rule_base <- getSimplRules
        let cont' = trimJoinCont var1 (idJoinPointHood var1) cont
            info = mkArgInfo env rule_base var1 cont'
        rebuildCall env info cont'

      DoneEx e mb_join -> simplExprF env' e cont'
        where
          cont' = trimJoinCont var mb_join cont
          env' = zapSubstEnv env

rebuildCall
  :: SimplEnv
  -> ArgInfo
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)

-- Bottoming applications
rebuildCall env ArgInfo{ ai_fun = fun, ai_args = rev_args, ai_dmds = [] } cont
  | not (contIsTrivial cont)
  = seqType cont_ty `seq`
    return (emptyFloats env, castBottomExpr res cont_ty)
  where
    res = argInfoExpr fun rev_args
    cont_ty = contResultType cont

-- Try inlining 
rebuildCall env info@ArgInfo{ ai_fun = fun, ai_args = rev_args, ai_rewrite = TryInlining } cont
  = do logger <- getLogger
       let full_cont = pushSimplifiedRevArgs env rev_args cont
       mb_inline <- tryInlining env logger fun full_cont
       case mb_inline of
         Just expr -> do
           checkedTick (UnfoldingDone fun)
           let env1 = zapSubstEnv env
           simplExprF env1 expr full_cont
         Nothing -> rebuildCall env (info { ai_rewrite = TryNothing }) cont

-- Trye rewrite rules
rebuildCall env info@ArgInfo{ ai_fun = fun, ai_args = rev_args
                            , ai_rewrite = TryRules nr_wanted rules } cont
  | nr_wanted == 0 || no_more_args
  = do mb_match <- tryRules env rules fun (reverse rev_args) cont
       case mb_match of
         Just (env', rhs, cont') -> simplExprF env' rhs cont'
         Nothing -> rebuildCall env (info { ai_rewrite = TryInlining }) cont
  where
    no_more_args = case cont of
      ApplyToTy{} -> False
      ApplyToKiCo{} -> False
      ApplyToKi{} -> False
      ApplyToVal{} -> False
      _ -> True

-- Simplify type applications and casts
rebuildCall env info CastIt{ sc_co = co, sc_opt = opt, sc_cont = cont }
  = rebuildCall env (addCastTo info co') cont
  where
    co' = optOutTyCoercion env co opt

rebuildCall env info ApplyToTy{ sc_arg_ty = arg_ty, sc_hole_ty = hole_ty, sc_cont = cont }
  = rebuildCall env (addTyArgTo info arg_ty hole_ty) cont

rebuildCall env info ApplyToKiCo{ sc_arg_kico = arg_kico, sc_hole_ty = hole_ty, sc_cont = cont }
  = rebuildCall env (addKiCoArgTo info arg_kico hole_ty) cont

rebuildCall env info ApplyToKi{ sc_arg_ki = arg_ki, sc_hole_ty = hole_ty, sc_cont = cont }
  = rebuildCall env (addKiArgTo info arg_ki hole_ty) cont

-- rebuildCall env ArgInfo{ ai_fun = fun_id, ai_args = rev_args }
--                 ApplyToVal{ sc_arg = arg, sc_env = arg_se, sc_cont = cont, sc_hole_ty = fun_ty }
  -- TODO: | fun_id `hasKey` runRWKey

-- Simplify value arguments
rebuildCall env fun_info ApplyToVal{ sc_arg = arg, sc_env = arg_se, sc_dup = dup_flag
                                   , sc_hole_ty = fun_ty, sc_cont = cont }
  | isSimplified dup_flag
  = rebuildCall env (addValArgTo fun_info arg fun_ty) cont

  | seCaseCase env
  = simplExprF (arg_se `setInScopeFromE` env) arg
    (StrictArg { sc_fun = fun_info
               , sc_fun_ty = fun_ty
               , sc_dup = Simplified
               , sc_cont = cont })

  | otherwise
  = do (_, _, arg') <- simplArg env dup_flag fun_ty (Just fun_info) arg_se arg
       rebuildCall env (addValArgTo fun_info arg' fun_ty) cont

rebuildCall env ArgInfo{ ai_fun = fun, ai_args = rev_args } cont
  = rebuild env (argInfoExpr fun rev_args) cont

tryInlining :: SimplEnv -> Logger -> OutId -> SimplCont -> SimplM (Maybe OutExpr)
tryInlining env logger var cont
  | Just expr <- callSiteInline env logger var lone_variable arg_infos interesting_cont
  = do dump_inline expr cont
       return (Just expr)
  | otherwise
  = return Nothing
  where
    (lone_variable, arg_infos, call_cont) = contArgs cont
    interesting_cont = interestingCallContext env call_cont

    log_inlining doc
      = liftIO $ logDumpFile logger (mkDumpStyle alwaysQualify)
                 Opt_D_dump_inlinings "" FormatText doc

    dump_inline unfolding cont
      | not (logHasDumpFlag logger Opt_D_dump_inlinings) = return ()
      | not (logHasDumpFlag logger Opt_D_verbose_core2core)
      = when (isExternalName (varName var)) $ log_inlining $ sep [ text "Inlining done:"
                                                                 , nest 4 (ppr var) ]
      | otherwise
      = log_inlining $ sep [ text "Inlining done:" <+> ppr var
                           , nest 4 (vcat [ text "Inlined fn:" <+> nest 2 (ppr unfolding)
                                          , text "Cont:" <+> ppr cont ]) ]

{- *********************************************************************
*                                                                      *
                     Rewrite rules
*                                                                      *
********************************************************************* -}

tryRules
  :: SimplEnv
  -> [CoreRule]
  -> CoreId
  -> [ArgSpec]
  -> SimplCont
  -> SimplM (Maybe (SimplEnv, CoreExpr, SimplCont))
tryRules env rules fn args call_cont
  | null rules
  = return Nothing

  | Just (rule, rule_rhs) <- lookupRule ropts (getUnfoldingInRuleMatch env)
                             (activeRule (seMode env)) fn (argInfoAppArgs args) rules
  = do logger <- getLogger
       checkedTick (RuleFired (ruleName rule))
       let cont' = pushSimplifiedArgs zapped_env (drop (ruleArity rule) args) call_cont
           occ_anald_rhs = occurAnalyzeExpr rule_rhs
       dump logger rule rule_rhs
       return (Just (zapped_env, occ_anald_rhs, cont'))

  | otherwise
  = do logger <- getLogger
       nodump logger
       return Nothing
  where
    ropts = seRuleOpts env
    zapped_env = zapSubstEnv env

    printRuleModule rule = parens (maybe (text "BUILTIN")
                                   (pprModuleName . moduleName) (ruleModule rule))

    dump logger rule rule_rhs
      | logHasDumpFlag logger Opt_D_dump_rule_rewrites
      = log_rule Opt_D_dump_rule_rewrites "Rule fired" $
        vcat [ text "Rule:" <+> ftext (ruleName rule)
             , text "Module:" <+> printRuleModule rule
             , text "Before:" <+> hang (ppr fn) 2 (sep (map ppr args))
             , text "After:" <+> hang (pprCoreExpr rule_rhs) 2
               (sep $ map ppr $ drop (ruleArity rule) args)
             , text "Cont:" <+> ppr call_cont ]

      | logHasDumpFlag logger Opt_D_dump_rule_firings
      = log_rule Opt_D_dump_rule_firings "Rule fired" $
        ftext (ruleName rule) <+> printRuleModule rule

      | otherwise
      = return ()

    nodump logger
      | logHasDumpFlag logger Opt_D_dump_rule_rewrites
      = liftIO $ touchDumpFile logger Opt_D_dump_rule_rewrites
      | logHasDumpFlag logger Opt_D_dump_rule_firings
      = liftIO $ touchDumpFile logger Opt_D_dump_rule_firings
      | otherwise
      = return ()

    log_rule flag hdr details = do
      logger <- getLogger
      liftIO $ logDumpFile logger (mkDumpStyle alwaysQualify) flag "" FormatText
        $ sep [ text hdr, nest 4 details ]
      
{- *********************************************************************
*                                                                      *
                Rebuilding a case expression
*                                                                      *
********************************************************************* -}

rebuildCase
  :: SimplEnv
  -> OutExpr
  -> InId
  -> [InAlt]
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)

-- 1. Eliminate the case of a known constructor  
rebuildCase env scrut case_bndr alts cont
  | Lit lit <- scrut
  = do tick (KnownBranch case_bndr)
       case findAlt (LitAlt lit) alts of
         Nothing -> missingAlt env case_bndr alts cont
         Just (Alt _ bs rhs) -> simple_rhs env [] scrut bs rhs

  | Just (in_scope', wfloats, con, ty_args, other_args)
      <- exprIsConApp_maybe (getUnfoldingInRuleMatch env) scrut
  , let env0 = setInScopeSet env in_scope'
  = do tick (KnownBranch case_bndr)
       let case_bndr_rhs
             | exprIsTrivial scrut = scrut
             | otherwise = con_app
           con_app = Var (dataConId con) `mkTyApps` ty_args
                                         `mkCoreApps` other_args
       case findAlt (DataAlt con) alts of
         Nothing -> missingAlt env0 case_bndr alts cont
         Just (Alt DEFAULT bs rhs) -> simple_rhs env0 wfloats case_bndr_rhs bs rhs
         Just (Alt _ bs rhs) -> knownCon env0 scrut wfloats con ty_args other_args
                                         case_bndr bs rhs cont
  where
    simple_rhs env wfloats case_bndr_rhs bs rhs = assert (null bs) $ do
      (floats1, env') <- simplAuxBind "rebuildCase" env case_bndr case_bndr_rhs
      (floats2, expr') <- simplExprF env' rhs cont
      case wfloats of
        [] -> return (floats1 `addFloats` floats2, expr')
        _ -> return (emptyFloats env, Make.wrapFloats wfloats $
                                      wrapFloats (floats1 `addFloats` floats2) expr')

    -- TODO: GHC scales multiplicities here. We may have to alter the kinds!

-- 2. Eliminate case of an evaluated scrutinee
rebuildCase env scrut case_bndr alts@[Alt _ bndrs rhs] cont
  -- Case does not bind anything
  | is_plain_seq
  , exprOkToDiscard scrut
  = simplExprF env rhs cont

  -- Case to let
  | all_dead_bndrs
  , doCaseToLet scrut case_bndr
  = do tick (CaseElim case_bndr)
       (floats1, env') <- simplAuxBind "rebuildCaseAlt1" env case_bndr scrut
       (floats2, expr') <- simplExprF env' rhs cont
       return (floats1 `addFloats` floats2, expr')

  | is_plain_seq
  = reallyRebuildCase env scrut case_bndr alts cont

-- 3. Primop case-rules
  | Just (scrut', case_bndr', alts') <- caseRules2 scrut case_bndr alts
  = reallyRebuildCase env scrut' case_bndr' alts' cont

  where
    all_dead_bndrs = all isDeadBinder bndrs
    is_plain_seq = all_dead_bndrs && isDeadBinder case_bndr

rebuildCase env scrut case_bndr alts cont
  = reallyRebuildCase env scrut case_bndr alts cont
  
doCaseToLet :: OutExpr -> InId -> Bool
doCaseToLet scurt _ = exprOkForSpeculation scurt

reallyRebuildCase
  :: SimplEnv
  -> OutExpr
  -> InId
  -> [InAlt]
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)
reallyRebuildCase env scrut case_bndr alts cont
  | not (seCaseCase env)
  = do case_expr <- simplAlts env scrut case_bndr alts (mkBoringStop (contHoleType cont))
       rebuild env case_expr cont

  | otherwise
  = do (floats, env', cont') <- mkDupableCaseCont env alts cont
       case_expr <- simplAlts env' scrut case_bndr alts cont'
       return (floats, case_expr)
         -- TODO: scaling in case of case (we may need to adjust the kinds as above?)
         -- We may have to bail on case-of-case when the kinds aren't correct

simplAlts
  :: SimplEnv
  -> OutExpr
  -> InId
  -> [InAlt]
  -> SimplCont
  -> SimplM OutExpr
simplAlts env0 scrut case_bndr alts cont' = do
  traceSmpl "simplAlts"
    $ vcat [ ppr case_bndr
           , text "cont':" <+> ppr cont'
           , text "in_scope" <+> ppr (seInScope env0) ]

  (env1, case_bndr1) <- simplIdBinder env0 case_bndr
  let case_bndr2 = case_bndr1 `setIdUnfolding` evaldUnfolding
      env2 = modifyInScope env1 case_bndr2

  (imposs_deflt_cons, in_alts) <- prepareAlts scrut case_bndr alts

  alts' <- forM in_alts $
    simplAlt env2 (Just scrut) imposs_deflt_cons case_bndr (scrutOkForBinderSwap scrut) cont'

  let alts_ty' = contResultType cont'

  seqType alts_ty' `seq`
    mkCase (seMode env0) scrut case_bndr alts_ty' alts'

simplAlt
  :: SimplEnv
  -> Maybe OutExpr
  -> [AltCon]
  -> OutId
  -> BinderSwapDecision
  -> SimplCont
  -> InAlt
  -> SimplM OutAlt
simplAlt env _ impss_deflt_cons case_bndr bndr_swap cont (Alt DEFAULT bndrs rhs)
  = assert (null bndrs) $ do
      let env' = addDefaultUnfoldings env case_bndr bndr_swap impss_deflt_cons
      rhs' <- simplExprC env rhs cont
      return (Alt DEFAULT [] rhs')

simplAlt env _ _ case_bndr bndr_swap cont (Alt (LitAlt lit) bndrs rhs) = panic "simplAlt Lit"

simplAlt env scrut _ case_bndr bndr_swap cont (Alt (DataAlt con) vs rhs) = do
  let vs_with_info = adjustFieldsIdInfo scrut case_bndr bndr_swap con vs
  (env', vs') <- simplIdBinders env vs_with_info
  let inst_tys' = tyConAppArgs (varType case_bndr)
      con_app = mkConApp2 con inst_tys' vs'
      env'' = addAltUnfoldings env' case_bndr bndr_swap con_app
  rhs' <- simplExprC env'' rhs cont
  return (Alt (DataAlt con) vs' rhs')

adjustFieldsIdInfo
  :: Maybe OutExpr -> OutId -> BinderSwapDecision -> CoreDataCon -> [CoreId] -> [CoreId]
adjustFieldsIdInfo _ case_bndr bndr_swap con vs
  = go vs
  where
    go [] = []
    go (v:vs') = adjustFieldOccInfo case_bndr bndr_swap (v `setIdUnfolding` evaldUnfolding)
                 : go vs'
    
adjustFieldOccInfo :: OutId -> BinderSwapDecision -> CoreId -> CoreId
adjustFieldOccInfo case_bndr bndr_swap field_bndr
  | not (isDeadBinder case_bndr)
  = zapIdOccInfo field_bndr

  | DoBinderSwap{} <- bndr_swap
  = zapIdOccInfo field_bndr

  | otherwise
  = field_bndr

addDefaultUnfoldings :: SimplEnv -> OutId -> BinderSwapDecision -> [AltCon] -> SimplEnv
addDefaultUnfoldings env case_bndr bndr_swap imposs_deflt_cons
  = env2
  where
    unf = mkOtherCon imposs_deflt_cons
    env1 = addBinderUnfolding env case_bndr unf
    env2 | DoBinderSwap v _ <- bndr_swap
         = addBinderUnfolding env1 v unf
         | otherwise
         = env1

addAltUnfoldings :: SimplEnv -> OutId -> BinderSwapDecision -> OutExpr -> SimplEnv
addAltUnfoldings env case_bndr bndr_swap con_app
  = env2
  where
    con_app_unf = mk_simple_unf con_app
    env1 = addBinderUnfolding env case_bndr con_app_unf
    env2 | DoBinderSwap v mco <- bndr_swap
         = -- addBinderUnfolding env1 v $
           -- if isReflMCo mco
           -- then con_app_unf
           -- else mk_simple_unf (mkCaseMCo con_app mco)
             panic "addAltUnfoldings"
         | otherwise = env1

    !opts = seUnfoldingOpts env
    mk_simple_unf = mkSimpleUnfolding opts

addBinderUnfolding :: SimplEnv -> CoreId -> Unfolding -> SimplEnv
addBinderUnfolding env bndr unf
  | debugIsOn
  , Just tmpl <- maybeUnfoldingTemplate unf
  = warnPprTrace (not (eqType (varType bndr) (exprType tmpl)))
    "unfolding type mismatch"
    (ppr bndr $$ ppr (varType bndr) $$ ppr tmpl $$ ppr (exprType tmpl)) $
    modifyInScope env (bndr `setIdUnfolding` unf)
  | otherwise
  = modifyInScope env (bndr `setIdUnfolding` unf)

zapBndrOccInfo :: Bool -> CoreId -> CoreId
zapBndrOccInfo keep_occ_info pat_id
  | keep_occ_info = pat_id
  | otherwise = zapIdOccInfo pat_id

{- *********************************************************************
*                                                                      *
                Known constructor
*                                                                      *
********************************************************************* -}

knownCon
  :: SimplEnv
  -> OutExpr
  -> [FloatBind]
  -> CoreDataCon
  -> [OutType]
  -> [OutExpr]
  -> InId
  -> [InId]
  -> InExpr
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)
knownCon env scrut dc_floats dc dc_ty_args dc_args bndr bs rhs cont = do
  (floats1, env1) <- bind_args env bs dc_args
  (floats2, env2) <- bind_case_bndr env1
  (floats3, expr') <- simplExprF env2 rhs cont
  case dc_floats of
    [] -> return (floats1 `addFloats` floats2 `addFloats` floats3, expr')
    _ -> return (emptyFloats env,
                 Make.wrapFloats dc_floats $
                 wrapFloats (floats1 `addFloats` floats2 `addFloats` floats3) expr')
  where
    zap_occ = zapBndrOccInfo (isDeadBinder bndr)

    bind_args env' [] _ = return (emptyFloats env', env')
    bind_args env' (b:bs') (Type ty : args) = panic "bind_args Type"
    bind_args env' (b:bs') (KiCo co : args) = panic "bind_args KiCo"
    bind_args env' (b:bs') (Kind ki : args) = panic "bind_args Kind"
    bind_args env' (b:bs') (arg : args) = do
      let b' = zap_occ b
      (floats1, env2) <- simplAuxBind "knownCon" env' b' arg
      (floats2, env3) <- bind_args env2 bs' args
      return (floats1 `addFloats` floats2, env3)
    bind_args _ _ _ = pprPanic "bind_args" $ ppr dc $$ ppr bs $$ ppr dc_args $$
                      text "scrut:" <+> ppr scrut

    bind_case_bndr env
      | isDeadBinder bndr = return (emptyFloats env, env)
      | exprIsTrivial scrut = return ( emptyFloats env
                                     , extendIdSubst env bndr (DoneEx scrut NotJoinPoint) )
      | otherwise = do dc_args <- mapM (simplVar env) bs
                       let con_app = Var (dataConId dc)
                                     `mkTyApps` dc_ty_args
                                     `mkCoreApps` dc_args
                       simplAuxBind "case-bndr" env bndr con_app

missingAlt
  :: SimplEnv
  -> CoreId
  -> [InAlt]
  -> SimplCont
  -> SimplM (SimplFloats, OutExpr)
missingAlt env case_bndr _ cont
  = warnPprTrace True "missingAlt" (ppr case_bndr) $
    let cont_ty = contResultType cont
    in seqType cont_ty `seq`
       --return (emptyFloats env, mkImpossibleExpr cont_ty "Simplify.Iteration.missingAlt")
       panic "missingAlt"

{- *********************************************************************
*                                                                      *
                Duplicating continuations
*                                                                      *
********************************************************************* -}

mkDupableCaseCont
  :: SimplEnv
  -> [InAlt]
  -> SimplCont
  -> SimplM (SimplFloats, SimplEnv, SimplCont)
mkDupableCaseCont env alts cont
  | altsWouldDup alts = do
      (floats, cont) <- mkDupableCont env cont
      let env' = bumpCaseDepth $ env `setInScopeFromF` floats
      return (floats, env', cont)
  | otherwise = return (emptyFloats env, env, cont)

altsWouldDup :: [InAlt] -> Bool
altsWouldDup [] = False
altsWouldDup [_] = False
altsWouldDup (alt:alts)
  | is_bot_alt alt = altsWouldDup alts
  | otherwise = not (all is_bot_alt alts)
  where
    is_bot_alt (Alt _ _ rhs) = panic "exprIsDeadEnd rhs"

mkDupableCont
  :: SimplEnv
  -> SimplCont
  -> SimplM (SimplFloats, SimplCont)
mkDupableCont env cont = mkDupableContWithDmds env (repeat topDmd) cont

mkDupableContWithDmds
  :: SimplEnv
  -> [Demand]
  -> SimplCont
  -> SimplM (SimplFloats, SimplCont)
mkDupableContWithDmds env _ cont
  | contIsDupable cont
  = return (emptyFloats env, cont)

mkDupableContWithDmds _ _ Stop{} = panic "mkDupableCont"

mkDupableContWithDmds env dmds CastIt{ sc_co = co, sc_opt = opt, sc_cont = cont } = do
  (floats, cont') <- mkDupableContWithDmds env dmds cont
  return (floats, CastIt{ sc_co = optOutTyCoercion env co opt
                        , sc_opt = True
                        , sc_cont = cont' })

mkDupableContWithDmds env dmds (TickIt t cont) = do
  (floats, cont') <- mkDupableContWithDmds env dmds cont
  return (floats, TickIt t cont')

mkDupableContWithDmds env _ StrictBind{ sc_bndr = bndr, sc_body = body, sc_from = from_what
                                      , sc_env = se, sc_cont = cont }
  = do let sb_env = se `setInScopeFromE` env
       (sb_env1, bndr') <- simplIdBinder sb_env bndr
       (floats1, join_inner) <- simplNonRecBody sb_env1 from_what body cont
       let join_body = wrapFloats floats1 join_inner
           res_ty = contResultType cont
       mkDupableStrictBind env bndr' join_body res_ty

mkDupableContWithDmds env _ StrictArg{ sc_fun = fun, sc_cont = cont, sc_fun_ty = fun_ty }
  | isNothing (isDataConId_maybe (ai_fun fun))
  , thumbsUpPlanA cont
  = do let dmds = tail $ ai_dmds fun
       (floats1, cont') <- mkDupableContWithDmds env dmds cont
       (floats_s, args') <- mapAndUnzipM (makeTrivialArg env) (ai_args fun)
       return ( foldl' addLetFloats floats1 floats_s
              , StrictArg { sc_fun = fun { ai_args = args' }
                          , sc_cont = cont'
                          , sc_fun_ty = fun_ty
                          , sc_dup = OkToDup } )
  | otherwise
  = do let rhs_ty = contResultType cont
           (arg_ty, _, _) = splitFunTy fun_ty
       arg_bndr <- newId (fsLit "arg") arg_ty
       let env' = env `addNewInScopeIds` [arg_bndr]
       (floats, join_rhs) <- rebuildCall env' (addValArgTo fun (Var arg_bndr) fun_ty) cont
       mkDupableStrictBind env' arg_bndr (wrapFloats floats join_rhs) rhs_ty
  where
    thumbsUpPlanA StrictArg{} = False
    thumbsUpPlanA StrictBind{} = True
    thumbsUpPlanA Stop{} = True
    thumbsUpPlanA Select{} = True
    thumbsUpPlanA CastIt{ sc_cont = k } = thumbsUpPlanA k
    thumbsUpPlanA (TickIt _ k) = thumbsUpPlanA k
    thumbsUpPlanA ApplyToVal{ sc_cont = k } = thumbsUpPlanA k
    thumbsUpPlanA ApplyToTy{ sc_cont = k } = thumbsUpPlanA k
    thumbsUpPlanA ApplyToKiCo{ sc_cont = k } = thumbsUpPlanA k
    thumbsUpPlanA ApplyToKi{ sc_cont = k } = thumbsUpPlanA k

mkDupableContWithDmds env dmds ApplyToTy{ sc_cont = cont, sc_arg_ty = arg_ty
                                        , sc_hole_ty = hole_ty }
  = do (floats, cont') <- mkDupableContWithDmds env dmds cont
       return (floats, ApplyToTy { sc_cont = cont'
                                 , sc_arg_ty = arg_ty
                                 , sc_hole_ty = hole_ty })

mkDupableContWithDmds env dmds ApplyToKiCo{ sc_cont = cont, sc_arg_kico = arg_kico
                                          , sc_hole_ty = hole_ty }
  = do (floats, cont') <- mkDupableContWithDmds env dmds cont
       return (floats, ApplyToKiCo { sc_cont = cont'
                                   , sc_arg_kico = arg_kico
                                   , sc_hole_ty = hole_ty })

mkDupableContWithDmds env dmds ApplyToKi{ sc_cont = cont, sc_arg_ki = arg_ki
                                        , sc_hole_ty = hole_ty }
  = do (floats, cont') <- mkDupableContWithDmds env dmds cont
       return (floats, ApplyToKi { sc_cont = cont'
                                 , sc_arg_ki = arg_ki
                                 , sc_hole_ty = hole_ty })

mkDupableContWithDmds env dmds ApplyToVal{ sc_arg = arg, sc_dup = dup, sc_env = se
                                         , sc_cont = cont, sc_hole_ty = hole_ty }
  = do let (dmd, cont_dmds) = (head dmds, tail dmds)
       (floats1, cont') <- mkDupableContWithDmds env cont_dmds cont
       let env' = env `setInScopeFromF` floats1
       (_, se', arg') <- simplArg env' dup hole_ty Nothing se arg
       (let_floats2, arg'') <- makeTrivial env NotTopLevel dmd (fsLit "karg") arg'
       let all_floats = floats1 `addLetFloats` let_floats2
       return ( all_floats
              , ApplyToVal { sc_arg = arg''
                           , sc_env = se' `setInScopeFromF` all_floats
                           , sc_dup = OkToDup
                           , sc_cont = cont'
                           , sc_hole_ty = hole_ty } )

mkDupableContWithDmds env _ Select{ sc_bndr = case_bndr
                                  , sc_alts = alts
                                  , sc_env = se
                                  , sc_cont = cont }
  = do tick (CaseOfCase case_bndr)
       (floats, alt_env, alt_cont) <- mkDupableCaseCont (se `setInScopeFromE` env) alts cont
       (alt_env', case_bndr') <- simplIdBinder alt_env case_bndr
       alts' <- forM alts $ simplAlt alt_env' Nothing [] case_bndr' NoBinderSwap alt_cont
       (join_floats, alts'') <- mapAccumLM (mkDupableAlt env case_bndr') emptyJoinFloats alts'
       let all_floats = floats `addJoinFloats` join_floats
       return ( all_floats
              , Select { sc_dup = OkToDup
                       , sc_bndr = case_bndr'
                       , sc_alts = alts''
                       , sc_env = zapSubstEnv se `setInScopeFromF` all_floats
                       , sc_cont = mkBoringStop (contResultType cont) } )

mkDupableStrictBind
  :: SimplEnv
  -> OutId
  -> OutExpr
  -> OutType
  -> SimplM (SimplFloats, SimplCont)
mkDupableStrictBind env arg_bndr join_rhs res_ty
  | uncondInlineJoin [C.Id arg_bndr] join_rhs
  = return ( emptyFloats env
           , StrictBind { sc_bndr = arg_bndr
                        , sc_body = join_rhs
                        , sc_env = zapSubstEnv env
                        , sc_from = FromLet
                        , sc_dup = OkToDup
                        , sc_cont = mkBoringStop res_ty } )
  | otherwise
  = do join_bndr <- newJoinId [(C.Id arg_bndr, Just (BIKi UKd))] res_ty -- TODO: double check kind
       let arg_info = ArgInfo { ai_fun = join_bndr
                              , ai_rewrite = TryNothing
                              , ai_args = []
                              , ai_encl = False
                              , ai_dmds = repeat topDmd
                              , ai_discs = repeat 0 }
       return ( addJoinFloats (emptyFloats env)
              $ unitJoinFloat
              $ NonRec join_bndr
              $ Lam (C.Id $ setOneShotLambda arg_bndr) (Just (BIKi LKd)) join_rhs
                -- TODO: double check the kind
              , StrictArg { sc_dup = OkToDup
                          , sc_fun = arg_info
                          , sc_fun_ty = varType join_bndr
                          , sc_cont = mkBoringStop res_ty } )

mkDupableAlt
  :: SimplEnv
  -> OutId
  -> JoinFloats
  -> OutAlt
  -> SimplM (JoinFloats, OutAlt)
mkDupableAlt _ case_bndr jfloats (Alt con alt_bndrs alt_rhs_in)
  | uncondInlineJoin (C.Id <$> alt_bndrs) alt_rhs_in
  = return (jfloats, Alt con alt_bndrs alt_rhs_in)
  | otherwise
  = do let rhs_ty' = exprType alt_rhs_in

           abstracted_binders = abstract_binders alt_bndrs

           abstract_binders :: [CoreId] -> [(CoreBndr, Maybe CoreMonoKind)] -- TODO: check kinds
           abstract_binders []
             | isDeadBinder case_bndr = []
             | otherwise = [(C.Id case_bndr, Just (BIKi UKd))]
           abstract_binders (alt_bndr : alt_bndrs)
             | isDeadBinder alt_bndr = abstract_binders alt_bndrs
             | otherwise = (C.Id alt_bndr, Just (BIKi UKd)) : abstract_binders alt_bndrs

           final_args = map (bndrToCoreExpr . fst) abstracted_binders

           final_bndrs = map one_shot abstracted_binders
           one_shot (C.Id v, ki) = (C.Id $ setOneShotLambda v, ki)
           one_shot (v, ki) = (v, ki)

           join_rhs = mkCoreLams (mapFst zapBndrUnfolding final_bndrs) alt_rhs_in

       join_bndr <- newJoinId abstracted_binders rhs_ty'
       let join_call = mkCoreApps (Var join_bndr) final_args
           alt' = Alt con alt_bndrs join_call

       return ( jfloats `addJoinFlts` unitJoinFloat (NonRec join_bndr join_rhs)
              , alt' )

{- *********************************************************************
*                                                                      *
                Unfoldings
*                                                                      *
********************************************************************* -}

simplLetUnfolding
  :: SimplEnv
  -> BindContext
  -> InId
  -> OutExpr
  -> OutType
  -> ArityType
  -> Unfolding
  -> SimplM Unfolding
simplLetUnfolding env bind_cxt id new_rhs rhs_ty arity unf
  | isStableUnfolding unf
  = simplStableUnfolding env bind_cxt id rhs_ty arity unf

  | freshly_born_join_point id
  = return noUnfolding

  | isExitJoinId id
  = return noUnfolding

  | otherwise
  = mkLetUnfolding env (bindContextLevel bind_cxt) VanillaSrc id is_join_point new_rhs
  where
    is_join_point = isJoinId id
    freshly_born_join_point id = is_join_point && isManyOccs (idOccInfo id)

mkLetUnfolding
  :: SimplEnv
  -> TopLevelFlag
  -> UnfoldingSource
  -> InId
  -> Bool
  -> OutExpr
  -> SimplM Unfolding
mkLetUnfolding env top_lvl src id is_join new_rhs
  = return (mkUnfolding uf_opts src is_top_lvl is_bottoming is_join new_rhs Nothing)
  where
    !uf_opts = seUnfoldingOpts env
    !is_top_lvl = isTopLevel top_lvl
    !is_bottoming = isDeadEndId id

simplStableUnfolding
  :: SimplEnv
  -> BindContext
  -> InId
  -> OutType
  -> ArityType
  -> Unfolding
  -> SimplM Unfolding
simplStableUnfolding env bind_cxt id rhs_ty id_arity unf
  = case unf of
      NoUnfolding -> return unf
      OtherCon{} -> return unf
      CoreUnfolding { uf_tmpl = expr, uf_src = src, uf_guidance = guide }
        | isStableSource src
        -> do expr' <- case bind_cxt of
                BC_Join _ cont -> simplJoinRhs unf_env id expr cont
                BC_Let _ is_rec -> do let cont = mkRhsStop rhs_ty is_rec topDmd
                                      expr' <- simplExprC unf_env expr cont
                                      return (eta_expand expr')
              case guide of
                UnfWhen { ug_boring_ok = boring_ok }
                  -> let !new_boring_ok = boring_ok || panic "inlineBoringOk expr'"
                         guide' = guide { ug_boring_ok = new_boring_ok }

                     in return $ mkCoreUnfolding src is_top_lvl expr' Nothing guide'
                _ -> mkLetUnfolding env top_lvl src id False expr'

        | otherwise -> return noUnfolding
  where
    top_lvl = bindContextLevel bind_cxt
    !is_top_lvl = isTopLevel top_lvl
    act = idInlineActivation id
    unf_env = updMode (updModeForStableUnfoldings act) env

    eta_expand expr
      | seEtaExpand env
      , panic "exprArity expr" < arityTypeArity id_arity
      , wantEtaExpansion expr
      = etaExpandAT (getInScope env) id_arity expr
      | otherwise
      = expr

{- *********************************************************************
*                                                                      *
                    Rules
*                                                                      *
********************************************************************* -}
      
addBndrRules
  :: SimplEnv
  -> InId
  -> OutId
  -> BindContext
  -> SimplM (SimplEnv, OutId)
addBndrRules env in_id out_id bind_cxt
  | null old_rules
  = return (env, out_id)
  | otherwise
  = do new_rules <- simplRules env (Just out_id) old_rules bind_cxt
       let final_id = out_id `setIdSpecialization` panic "mkRuleInfo new_rules"
       return (modifyInScope env final_id, final_id)
  where
    old_rules = ruleInfoRules (idSpecialization in_id)

simplImpRules :: SimplEnv -> [CoreRule] -> SimplM [CoreRule]
simplImpRules env rules = simplRules env Nothing rules (BC_Let TopLevel NonRecursive)

simplRules
  :: SimplEnv
  -> Maybe OutId
  -> [CoreRule]
  -> BindContext
  -> SimplM [CoreRule]
simplRules env mb_new_id rules bind_cxt
  = mapM simpl_rule rules
  where
    simpl_rule rule@BuiltinRule{} = return rule
    simpl_rule rule@Rule{ ru_bndrs = bndrs
                        , ru_args = args
                        , ru_fn = fn_name
                        , ru_rhs = rhs
                        , ru_act = act }
      = do (env', bndrs_as) <- simplBinders env (bndrs `zip` (repeat ()))
           let bndrs' = fst <$> bndrs_as
           let rhs_ty = substTy env' (exprType rhs)
               rhs_cont = case bind_cxt of
                            BC_Let{} -> mkBoringStop rhs_ty
                            BC_Join _ cont -> assertPpr join_ok bad_join_msg cont
               lhs_env = updMode updModeForRules env'
               rhs_env = updMode (updModeForStableUnfoldings act) env'

               !fn_name' = case mb_new_id of
                             Just id -> varName id
                             Nothing -> fn_name

               join_ok = case mb_new_id of
                           Just id | JoinPoint join_arity <- idJoinPointHood id
                                   -> length args == join_arity
                           _ -> False
               bad_join_msg = vcat [ ppr mb_new_id
                                   , ppr rule
                                   , ppr (fmap idJoinPointHood mb_new_id) ]

           args' <- mapM (simplExpr lhs_env) args
           rhs' <- simplExprC rhs_env rhs rhs_cont
           return $ rule { ru_bndrs = bndrs'
                         , ru_fn = fn_name'
                         , ru_args = args'
                         , ru_rhs = occurAnalyzeExpr rhs' }
