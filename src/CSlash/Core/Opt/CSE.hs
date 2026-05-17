module CSlash.Core.Opt.CSE (cseProgram, cseOneExpr) where

import CSlash.Core.Subst
import CSlash.Types.Var.Env ( mkInScopeSet )
import CSlash.Types.Var
import CSlash.Types.Var.Id
import CSlash.Core.Utils   ( {-, exprIsTickedString
                           ,-} stripTicksE, stripTicksT, mkTicks )
import CSlash.Core.Make (mkAltExpr, mkCoreLams)       
import CSlash.Core.FVs     ( exprFreeVars )
import CSlash.Core.Type    ( tyConAppArgs )
import CSlash.Core.Kind
import CSlash.Core as C
import CSlash.Utils.Outputable
import CSlash.Types.Basic
import CSlash.Types.Tickish
import CSlash.Core.Map.Expr
import CSlash.Utils.Misc   ( filterOut, equalLength )
import CSlash.Utils.Panic
import Data.Functor.Identity ( Identity (..) )
import Data.List        ( mapAccumL )

{- *********************************************************************
*                                                                      *
        Common subexpression
*                                                                      *
********************************************************************* -}

cseProgram :: CoreProgram -> CoreProgram
cseProgram binds = snd (mapAccumL (cseBind TopLevel) emptyCSEnv binds)

cseBind :: TopLevelFlag -> CSEnv -> CoreBind -> (CSEnv, CoreBind)
cseBind toplevel env (NonRec b e)
  = (env2, NonRec b2 e2)
  where
    (env1, b1) = addBinder env b
    (env2, (b2, e2)) = cse_bind toplevel env env1 (b, e) b1

cseBind toplevel env (Rec [(in_id, rhs)])
  | noCSE in_id
  = (env1, Rec [(out_id, rhs')])

  | Just previous <- lookupCSRecEnv env out_id rhs''
  = let previous' = mkTicks ticks previous
        out_id' = delayInlining toplevel out_id
    in (extendCSSubst env1 in_id previous', NonRec out_id' previous')

  | otherwise
  = (extendCSRecEnv env1 out_id rhs'' id_expr', Rec [(zapped_id, rhs')])

  where
    (env1, Identity out_id) = addRecBinders env (Identity in_id)
    rhs' = cseExpr env1 rhs
    rhs'' = stripTicksE tickishFloatable rhs'
    ticks = stripTicksT tickishFloatable rhs'
    id_expr' = varToCoreExpr out_id
    zapped_id = zapIdUsageInfo out_id

cseBind toplevel env (Rec pairs)
  = (env2, Rec pairs')
  where
    (env1, bndrs1) = addRecBinders env (map fst pairs)
    (env2, pairs') = mapAccumL do_one env1 (zip pairs bndrs1)

    do_one env (pr, b1) = cse_bind toplevel env env pr b1

cse_bind :: TopLevelFlag -> CSEnv -> CSEnv -> (InId, InExpr) -> OutId -> (CSEnv, (OutId, OutExpr))
cse_bind toplevel env_rhs env_body (in_id, in_rhs) out_id
  | isTopLevel toplevel, panic "exprIsTickedString in_rhs"
  = (env_body', (out_id', in_rhs))

  | JoinPoint arity <- idJoinPointHood out_id
  = let (params, in_body) = collectNBinders arity in_rhs
        (env', params') = addLamBinders env_rhs params
        out_body = tryForCSE env' in_body
    in (env_body, (out_id, mkCoreLams params' out_body))

  | otherwise
  = (env_body', (out_id'', out_rhs))
  where
    (env_body', out_id') = extendCSEnvWithBinding env_body in_id out_id out_rhs cse_done
    (cse_done, out_rhs) = try_for_cse env_rhs in_rhs
    out_id'' | cse_done = zapStableUnfolding $ delayInlining toplevel out_id'
             | otherwise = out_id'

delayInlining :: TopLevelFlag -> CoreId -> CoreId
delayInlining top_lvl bndr
  | isTopLevel top_lvl
  , isAlwaysActive (idInlineActivation bndr)
  , idHasRules bndr
  = bndr `setInlineActivation` activateAfterInitial
  | otherwise
  = bndr

extendCSEnvWithBinding :: CSEnv -> InId -> OutId -> OutExpr -> Bool -> (CSEnv, OutId)
extendCSEnvWithBinding env in_id out_id rhs' cse_done
  | noCSE out_id = (env, out_id)
  | use_subst = (extendCSSubst env in_id rhs', out_id)
  | cse_done = (env, out_id)
  | otherwise = (extendCSEnv env rhs' id_expr', zapped_id)
  where
    id_expr' = varToCoreExpr out_id
    zapped_id = zapIdUsageInfo out_id

    use_subst | Var{} <- rhs' = True
              | otherwise = False

noCSE :: InId -> Bool
noCSE id
  | isJoinId id = no_cse
  | isStableUserUnfolding unf = no_cse
  | user_activation_control = no_cse
  | otherwise = yes_cse
  where
    unf = idUnfolding id
    user_activation_control = not (isAlwaysActive (idInlineActivation id))
                              && not (noUserInlineSpec (inlinePragmaSpec (idInlinePragma id)))
    yes_cse = False
    no_cse = True

tryForCSE :: CSEnv -> InExpr -> OutExpr
tryForCSE env expr = snd (try_for_cse env expr)

try_for_cse :: CSEnv -> InExpr -> (Bool, OutExpr)
try_for_cse env expr
  | Just e <- lookupCSEnv env expr'' = (True, mkTicks ticks e)
  | otherwise = (False, expr')
  where
    expr' = cseExpr env expr
    expr'' = stripTicksE tickishFloatable expr'
    ticks = stripTicksT tickishFloatable expr'

cseOneExpr :: InExpr -> OutExpr
cseOneExpr e = cseExpr env e
  where
    env = emptyCSEnv { cs_subst = mkEmptyTermSubst (exprFreeVars e) }

cseExpr :: CSEnv -> InExpr -> OutExpr
cseExpr env (Type t) = Type (substTyUnchecked (csEnvSubst env) t)
cseExpr env (KiCo c) = KiCo (substKiCo (csEnvSubst env) c)
cseExpr env (Kind k) = Kind (substMonoKiUnchecked (csEnvSubst env) k)
cseExpr _ (Lit lit) = Lit lit
cseExpr env (Var v) = lookupSubst env v
cseExpr env (App f a) = App (cseExpr env f) (tryForCSE env a)
cseExpr env (Tick t e) = Tick t (cseExpr env e)
cseExpr env (Cast e co) = Cast (tryForCSE env e) (panic "substTyCo (csEnvSubst env) co")
cseExpr env (Lam b k e)
  = let (env', (b', k')) = addLamBinder env (b, k)
    in Lam b' k' (cseExpr env' e)
cseExpr env (Let bind e)
  = let (env', bind') = cseBind NotTopLevel env bind
    in Let bind' (cseExpr env' e)
cseExpr env (Case e bndr ty alts) = cseCase env e bndr ty alts

cseCase :: CSEnv -> InExpr -> InId -> InType -> [InAlt] -> OutExpr
cseCase env scrut bndr ty alts
  = Case scrut1 bndr3 ty' $ combineAlts (map cse_alt alts)
  where
    ty' = substTyUnchecked (csEnvSubst env) ty
    (cse_done, scrut1) = try_for_cse env scrut

    bndr1 = zapIdOccInfo bndr

    (env1, bndr2) = addBinder env bndr1
    (alt_env, bndr3) = extendCSEnvWithBinding env1 bndr bndr2 scrut1 cse_done

    con_target :: OutExpr
    con_target = lookupSubst alt_env bndr
    
    arg_tys :: [OutType]
    arg_tys = tyConAppArgs (varType bndr3)

    cse_alt (Alt (DataAlt con) args rhs)
      = Alt (DataAlt con) args' (tryForCSE new_env rhs)
      where
        (env', args') = addBinders alt_env args
        new_env = extendCSEnv env' con_expr con_target
        con_expr = mkAltExpr (DataAlt con) args' arg_tys

    cse_alt (Alt con args rhs)
      = Alt con args' (tryForCSE env' rhs)
      where
        (env', args') = addBinders alt_env args
    
combineAlts :: [OutAlt] -> [OutAlt]
combineAlts alts
  | (Just alt1, rest_alts) <- find_bndr_free_alt alts
  , Alt _ bndrs1 rhs1 <- alt1
  , let filtered_alts = filterOut (identical_alt rhs1) rest_alts
  , not (equalLength rest_alts filtered_alts)
  = assertPpr (all isDeadBinder bndrs1) (ppr alts) $
    Alt DEFAULT [] rhs1 : filtered_alts
  | otherwise
  = alts
  where
    find_bndr_free_alt :: [CoreAlt] -> (Maybe CoreAlt, [CoreAlt])
    find_bndr_free_alt [] = (Nothing, [])
    find_bndr_free_alt (alt@(Alt _ bndrs _) : alts)
      | all isDeadBinder bndrs = (Just alt, alts)
      | otherwise = case find_bndr_free_alt alts of
                      (mb_bf, alts) -> (mb_bf, alt:alts)

    identical_alt rhs1 (Alt _ _ rhs) = eqCoreExpr rhs1 rhs

{- *********************************************************************
*                                                                      *
               The CSE environment
*                                                                      *
********************************************************************* -}
        
data CSEnv = CS
  { cs_subst :: CoreSubst
  , cs_map :: CoreMap OutExpr
  , cs_rec_map :: CoreMap OutExpr
  }

emptyCSEnv :: CSEnv
emptyCSEnv = CS { cs_map = emptyCoreMap
                , cs_rec_map = emptyCoreMap
                , cs_subst = emptySubst }

lookupCSEnv :: CSEnv -> OutExpr -> Maybe OutExpr
lookupCSEnv  CS{ cs_map = csmap } expr
  = lookupCoreMap csmap expr

extendCSEnv :: CSEnv -> OutExpr -> OutExpr -> CSEnv
extendCSEnv cse expr triv_expr
  = cse { cs_map = extendCoreMap (cs_map cse) sexpr triv_expr }
  where
    sexpr = stripTicksE tickishFloatable expr

extendCSRecEnv :: CSEnv -> OutId -> OutExpr -> OutExpr -> CSEnv
extendCSRecEnv cse bndr expr triv_expr
  = cse { cs_rec_map = extendCoreMap (cs_rec_map cse)
                       (Lam (C.Id bndr) (Just (BIKi UKd)) expr) triv_expr }
    -- TODO: check this kind makes sense

lookupCSRecEnv :: CSEnv -> OutId -> OutExpr -> Maybe OutExpr
lookupCSRecEnv CS{ cs_rec_map = csmap } bndr expr
  = lookupCoreMap csmap (Lam (C.Id bndr) (Just (BIKi UKd)) expr) 

csEnvSubst :: CSEnv -> CoreSubst
csEnvSubst = cs_subst

lookupSubst :: CSEnv -> CoreId -> OutExpr
lookupSubst CS{ cs_subst = subst } x = lookupIdSubst subst x

extendCSSubst :: CSEnv -> CoreId -> CoreExpr -> CSEnv
extendCSSubst cse x rhs = cse { cs_subst = extendIdSubst (cs_subst cse) x rhs }

addBinder :: CSEnv -> CoreId -> (CSEnv, CoreId)
addBinder cse v = (cse { cs_subst = subst' }, v')
  where
    (subst', v') = substLetBndr (cs_subst cse) v

addBinders :: CSEnv -> [CoreId] -> (CSEnv, [CoreId])
addBinders cse vs = (cse { cs_subst = subst' }, vs')
  where
    (subst', vs') = substLetBndrs (cs_subst cse) vs

addLamBinder :: CSEnv -> (CoreBndr, Maybe CoreMonoKind) -> (CSEnv, (CoreBndr, Maybe CoreMonoKind))
addLamBinder cse v = (cse { cs_subst = subst' }, v')
  where
    (subst', v') = substLamBndr (cs_subst cse) v

addLamBinders
  :: CSEnv
  -> [(CoreBndr, Maybe CoreMonoKind)]
  -> (CSEnv, [(CoreBndr, Maybe CoreMonoKind)])
addLamBinders cse vs = (cse { cs_subst = subst' }, vs')
  where
    (subst', vs') = substLamBndrs (cs_subst cse) vs

{-# INLINE addRecBinders #-}
addRecBinders :: Traversable f => CSEnv -> f CoreId -> (CSEnv, f CoreId)
addRecBinders cse vs = let (subst', vs') = substLetRecBndrs (cs_subst cse) vs
                       in (cse { cs_subst = subst' }, vs')
