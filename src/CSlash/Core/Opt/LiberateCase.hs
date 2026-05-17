module CSlash.Core.Opt.LiberateCase (LibCaseOpts(..), liberateCase) where

import CSlash.Cs.Pass

import CSlash.Core as C
import CSlash.Core.Make
import CSlash.Core.Unfold
import CSlash.Core.Opt.Simplify.Inline
import CSlash.Builtin.Types ( unitDataConId )
import CSlash.Types.Var.Id
import CSlash.Types.Var.Env
import CSlash.Utils.Misc    ( notNull )
import CSlash.Utils.Panic

{- *********************************************************************
*                                                                      *
               Top-level code
*                                                                      *
********************************************************************* -}

liberateCase :: LibCaseOpts -> CoreProgram -> CoreProgram
liberateCase opts binds = do_prog (initLiberateCaseEnv opts) binds
  where
    do_prog _ [] = []
    do_prog env (bind:binds) = bind' : do_prog env' binds
                               where (env', bind') = libCaseBind env bind

initLiberateCaseEnv :: LibCaseOpts -> LibCaseEnv
initLiberateCaseEnv opts = LibCaseEnv
  { lc_opts = opts
  , lc_lvl = 0
  , lc_lvl_env = emptyVarEnv
  , lc_rec_env = emptyVarEnv
  , lc_scruts = []
  }

{- *********************************************************************
*                                                                      *
               Main payload
*                                                                      *
********************************************************************* -}

libCaseBind :: LibCaseEnv -> CoreBind -> (LibCaseEnv, CoreBind)
libCaseBind env (NonRec binder rhs)
  = (addBinders env [binder], NonRec binder (libCase env rhs))
libCaseBind env (Rec pairs)
  = (env_body, Rec pairs')
  where
    binders = map fst pairs

    env_body = addBinders env binders

    pairs' = [(binder, libCase env_rhs rhs) | (binder, rhs) <- pairs]

    env_rhs | is_dupable_bind = addRecBinds env dup_pairs
            | otherwise = env

    dup_pairs = [ (localizeId binder, libCase env_body rhs)
                | (binder, rhs) <- pairs ]

    is_dupable_bind = small_enough && all ok_pair pairs
   
    small_enough = case lc_threshold env of
                     Nothing -> True
                     Just size -> couldBeSmallEnoughToInline (lc_uf_opts env) size
                                  $ Let (Rec dup_pairs) (panic "Var unitDataConId")

    ok_pair (id, _) = idArity id > 0
                      && not (isDeadEndId id)

libCase :: LibCaseEnv -> CoreExpr -> CoreExpr
libCase env (Var v) = libCaseApp env v []
libCase _ (Lit lit) = Lit lit
libCase _ (Type ty) = Type ty
libCase _ (KiCo co) = KiCo co
libCase _ (Kind ki) = Kind ki
libCase env e@App{}
  | (Var v, args) <- collectArgs e
  = libCaseApp env v args
libCase env (App fun arg) = App (libCase env fun) (libCase env arg)
libCase env (Tick tickish body) = Tick tickish (libCase env body)
libCase env (Cast e co) = Cast (libCase env e) co
libCase env (Lam (C.Id binder) mki body)
  = Lam (C.Id binder) mki (libCase (addBinders env [binder]) body)
libCase env (Lam binder mki body)
  = Lam binder mki (libCase env body)
libCase env (Let bind body)
  = Let bind' (libCase env_body body)
  where
    (env_body, bind') = libCaseBind env bind
libCase env (Case scrut bndr ty alts)
  = Case (libCase env scrut) bndr ty (map (libCaseAlt env_alts) alts)
  where
    env_alts = addBinders (mk_alt_env scrut) [bndr]
    mk_alt_env (Var scrut_var) = addScrutedVar env scrut_var
    mk_alt_env (Cast scrut _) = mk_alt_env scrut
    mk_alt_env _ = env

libCaseAlt :: LibCaseEnv -> CoreAlt -> CoreAlt
libCaseAlt env (Alt con args rhs) = Alt con args (libCase (addBinders env args) rhs)


libCaseApp :: LibCaseEnv -> CoreId -> [CoreExpr] -> CoreExpr
libCaseApp env v args
  | Just the_bind <- lookupRecId env v
  , notNull free_scruts
  = Let the_bind expr'
  | otherwise
  = expr'
  where
    rec_id_level = lookupLevel env v
    free_scruts = freeScruts env rec_id_level
    expr' = mkCoreApps (Var v) (map (libCase env) args)

freeScruts :: LibCaseEnv -> LibCaseLevel -> [CoreId]
freeScruts env rec_bind_lvl
  = [ v | (v, scrut_bind_lvl, scrut_at_lvl) <- lc_scruts env
        , scrut_bind_lvl <= rec_bind_lvl
        , scrut_at_lvl > rec_bind_lvl ]

{- *********************************************************************
*                                                                      *
               Utility functions
*                                                                      *
********************************************************************* -}

addBinders :: LibCaseEnv -> [CoreId] -> LibCaseEnv
addBinders env@LibCaseEnv{ lc_lvl = lvl, lc_lvl_env = lvl_env } binders
  = env { lc_lvl_env = lvl_env' }
  where
    lvl_env' = extendVarEnvList lvl_env (binders `zip` repeat lvl)

addRecBinds :: LibCaseEnv -> [(CoreId, CoreExpr)] -> LibCaseEnv
addRecBinds env@LibCaseEnv{ lc_lvl = lvl, lc_lvl_env = lvl_env, lc_rec_env = rec_env } pairs
  = env { lc_lvl = lvl', lc_lvl_env = lvl_env', lc_rec_env = rec_env' }
  where
    lvl' = lvl + 1
    lvl_env' = extendVarEnvList lvl_env [(binder, lvl) | (binder, _) <- pairs]
    rec_env' = extendVarEnvList rec_env [(binder, Rec pairs) | (binder, _) <- pairs]

addScrutedVar :: LibCaseEnv -> CoreId -> LibCaseEnv
addScrutedVar env@LibCaseEnv{ lc_lvl = lvl, lc_lvl_env = lvl_env, lc_scruts = scruts } scrut_var
  | bind_lvl < lvl
  = env { lc_scruts = scruts' }
  | otherwise
  = env
  where
    scruts' = (scrut_var, bind_lvl, lvl) : scruts
    bind_lvl = case lookupVarEnv lvl_env scrut_var of
                 Just lvl -> lvl
                 Nothing -> topLevel

lookupRecId :: LibCaseEnv -> CoreId -> Maybe CoreBind
lookupRecId env id = lookupVarEnv (lc_rec_env env) id

lookupLevel :: LibCaseEnv -> CoreId -> LibCaseLevel
lookupLevel env id = case lookupVarEnv (lc_lvl_env env) id of
                       Just lvl -> lvl
                       Nothing -> topLevel

{- *********************************************************************
*                                                                      *
               Options
*                                                                      *
********************************************************************* -}

data LibCaseOpts = LibCaseOpts
  { lco_threshold :: !(Maybe Int)
  , lco_unfolding_opts :: !UnfoldingOpts
  }

{- *********************************************************************
*                                                                      *
               The environment
*                                                                      *
********************************************************************* -}
  
type LibCaseLevel = Int

topLevel :: LibCaseLevel
topLevel  = 0

lc_threshold :: LibCaseEnv -> Maybe Int
lc_threshold = lco_threshold . lc_opts

lc_uf_opts :: LibCaseEnv -> UnfoldingOpts
lc_uf_opts = lco_unfolding_opts . lc_opts

data LibCaseEnv = LibCaseEnv
  { lc_opts :: !LibCaseOpts
  , lc_lvl :: LibCaseLevel
  , lc_lvl_env :: IdEnv Zk LibCaseLevel
  , lc_rec_env :: IdEnv Zk CoreBind
  , lc_scruts :: [(CoreId, LibCaseLevel, LibCaseLevel)]
  }
