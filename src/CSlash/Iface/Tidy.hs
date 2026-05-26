{-# LANGUAGE BangPatterns #-}

{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module CSlash.Iface.Tidy where

import CSlash.Cs.Pass

import CSlash.Tc.Types
import CSlash.Tc.Utils.Env

import CSlash.Core
import CSlash.Core.Unfold
import CSlash.Core.Utils
-- import CSlash.Core.Unfold.Make
import CSlash.Core.FVs
import CSlash.Core.Tidy
import CSlash.Core.Seq         ( seqBinds )
import CSlash.Core.Opt.Arity   ( exprArity, typeArity, exprBotStrictness_maybe )
import CSlash.Core.Type
import CSlash.Core.Type.Tidy
import CSlash.Core.DataCon
import CSlash.Core.TyCon
import CSlash.Core.Opt.OccurAnal ( occurAnalyzeExpr )

import CSlash.Iface.Env

import CSlash.Utils.Outputable
import CSlash.Utils.Misc( filterOut )
import CSlash.Utils.Panic
import CSlash.Utils.Trace
import CSlash.Utils.Logger as Logger
import qualified CSlash.Utils.Error as Err

-- import CSlash.Types.ForeignStubs
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Var
import CSlash.Types.Var.Id
-- import CSlash.Types.Var.Id.Make ( mkDictSelRhs )
import CSlash.Types.Var.Id.Info
import CSlash.Types.Demand  ( isDeadEndAppSig, isNopSig, nopSig, isDeadEndSig )
import CSlash.Types.Basic
import CSlash.Types.Name hiding (varName)
import CSlash.Types.Name.Set
import CSlash.Types.Name.Cache
import CSlash.Types.Avail
import CSlash.Types.Tickish
import CSlash.Types.TypeEnv
import CSlash.Tc.Utils.TcType (tcSplitNestedSigmaTys)

import CSlash.Unit.Module
import CSlash.Unit.Module.ModGuts
import CSlash.Unit.Module.ModDetails
import CSlash.Unit.Module.Deps

import CSlash.Data.Maybe

import Control.Monad
import Data.Function
import Data.List        ( sortBy, mapAccumL )
import qualified Data.Set as S
-- import CSlash.Types.CostCentre

data UnfoldingExposure
  = ExposeNone
  | ExposeSome
  | ExposeOverloaded
  | ExposeAll
  deriving (Show, Eq, Ord)

data TidyOpts = TidyOpts
  { opt_name_cache :: !NameCache
  , opt_collect_ccs :: !Bool
  , opt_unfolding_opts :: !UnfoldingOpts
  , opt_expose_unfoldings :: !UnfoldingExposure
  , opt_trim_ids :: !Bool
  , opt_expose_rules :: !Bool
  , opt_keep_auto_rules :: !Bool
  }

tidyProgram :: TidyOpts -> ModGuts -> IO (CgGuts, ModDetails)
tidyProgram opts ModGuts{ mg_module = mod
                        , mg_exports = exports
                        , mg_binds = binds
                        , mg_rules = imp_rules
                        , mg_complete_matches = complete_matches
                        , mg_deps = deps
                        }
  = do let all_binds = binds

       (unfold_env, tidy_occ_env) <- chooseExternalIds opts mod all_binds imp_rules
       let (trimmed_binds, trimmed_rules) = findExternalRules opts all_binds imp_rules unfold_env

       (tidy_env, tidy_binds) <- tidyTopBinds unfold_env tidy_occ_env trimmed_binds

       panic "tidyProgram"

{- *********************************************************************
*                                                                      *
            Step 1: finding externals
*                                                                      *
********************************************************************* -}

type UnfoldEnv = IdEnv Zk (Name, Bool)

chooseExternalIds
  :: TidyOpts
  -> Module
  -> [CoreBind]
  -> [CoreRule]
  -> IO (UnfoldEnv, TidyOccEnv)
chooseExternalIds opts mod binds imp_id_rules = do
  (unfold_env1, occ_env1) <- search init_work_list emptyVarEnv init_occ_env
  let internal_ids = filter (not . (`elemVarEnv` unfold_env1)) binders
  tidy_internal internal_ids unfold_env1 occ_env1
  where
    name_cache = opt_name_cache opts

    init_work_list = zip init_ext_ids init_ext_ids
    init_ext_ids = sortBy (compare `on` getOccName) $ filter is_external binders

    is_external id
      | isExportedId id = True
      | opt_expose_rules opts = id `elemVarSet` rule_rhs_vars
      | otherwise = False

    rule_rhs_vars = mapUnionVarSet ruleRhsFreeIds imp_id_rules

    binders = map fst $ flattenBinds binds
    binder_set = mkVarSet binders

    avoids = [ getOccName name
             | bndr <- binders
             , let name = varName bndr
             , isExternalName name ]

    init_occ_env = initTidyOccEnv avoids

    search :: [(CoreId, CoreId)] -> UnfoldEnv -> TidyOccEnv -> IO (UnfoldEnv, TidyOccEnv)
    search [] unfold_env occ_env = return (unfold_env, occ_env)
    search ((idocc, referrer) : rest) unfold_env occ_env
      | idocc `elemVarEnv` unfold_env
      = search rest unfold_env occ_env
      | otherwise
      = do (occ_env', name') <- tidyTopName mod name_cache (Just referrer) occ_env idocc
           let (new_ids, show_unfold) = addExternal opts refined_id
               refined_id = case lookupVarSet binder_set idocc of
                              Just id -> id
                              Nothing -> warnPprTrace True "chooseExternalIds" (ppr idocc) idocc

               unfold_env' = extendVarEnv unfold_env idocc (name', show_unfold)
               referrer' | isExportedId refined_id = refined_id
                         | otherwise = referrer

           search (zip new_ids (repeat referrer') ++ rest) unfold_env' occ_env'

    tidy_internal :: [CoreId] -> UnfoldEnv -> TidyOccEnv -> IO (UnfoldEnv, TidyOccEnv)
    tidy_internal [] unfold_env occ_env = return (unfold_env, occ_env)
    tidy_internal (id:ids) unfold_env occ_env = do
      (occ_env', name') <- tidyTopName mod name_cache Nothing occ_env id
      let unfold_env' = extendVarEnv unfold_env id (name', False)
      tidy_internal ids unfold_env' occ_env'

addExternal :: TidyOpts -> CoreId -> ([CoreId], Bool)
addExternal opts id
  | ExposeNone <- opt_expose_unfoldings opts
  , not (isCompulsoryUnfolding unfolding)
  = ([], False)

  | otherwise
  = panic "(new_needed_ids, show_unfold)"

  where
    idinfo = idInfo id
    unfolding = realUnfoldingInfo idinfo

{- *********************************************************************
*                                                                      *
               findExternalRules
*                                                                      *
********************************************************************* -}

findExternalRules
  :: TidyOpts
  -> [CoreBind]
  -> [CoreRule]
  -> UnfoldEnv
  -> ([CoreBind], [CoreRule])
findExternalRules opts binds imp_id_rules unfold_env
  = (trimmed_binds, filter keep_rule all_rules)
  where
    imp_rules | opt_expose_rules opts = filter expose_rule imp_id_rules
              | otherwise = []

    imp_user_rule_fvs = mapUnionVarSet user_rule_rhs_fvs imp_rules

    user_rule_rhs_fvs rule
      | isAutoRule rule && not (opt_keep_auto_rules opts)
      = emptyVarSet
      | otherwise
      = ruleRhsFreeIds rule

    (trimmed_binds, local_bndrs, _, all_rules) = trim_binds binds

    keep_rule rule = ruleFreeIds rule `subVarSet` local_bndrs

    expose_rule rule = all is_external_id (ruleLhsFreeIdsList rule)

    is_external_id id = case lookupVarEnv unfold_env id of
      Just (name, _) -> isExternalName name && not (isImplicitId id)
      Nothing -> False

    trim_binds :: [CoreBind] -> ([CoreBind], CoreIdSet, CoreIdSet, [CoreRule])
    trim_binds [] = ([], emptyVarSet, imp_user_rule_fvs, imp_rules)
    trim_binds (bind:binds)
      | any needed bndrs
      = (bind : binds', bndr_set', needed_fvs', local_rules ++ rules)
      | otherwise
      = stuff
      where
        stuff@(binds', bndr_set, needed_fvs, rules) = trim_binds binds

        needed bndr = isExportedId bndr || bndr `elemVarSet` needed_fvs

        bndrs = bindersOf bind
        rhss = rhssOfBind bind
        bndr_set' = bndr_set `extendVarSetList` bndrs

        needed_fvs' = needed_fvs `unionVarSet`
                      mapUnionVarSet idUnfoldingIds bndrs `unionVarSet`
                      mapUnionVarSet exprFreeIds rhss `unionVarSet`
                      mapUnionVarSet user_rule_rhs_fvs local_rules

        local_rules = [ rule
                      | opt_expose_rules opts
                      , id <- bndrs
                      , is_external_id id
                      , rule <- idCoreRules id
                      , expose_rule rule ]

{- *********************************************************************
*                                                                      *
               tidyTopName
*                                                                      *
********************************************************************* -}

tidyTopName
  :: Module
  -> NameCache
  -> Maybe CoreId
  -> TidyOccEnv
  -> CoreId
  -> IO (TidyOccEnv, Name)
tidyTopName mod name_cache maybe_ref occ_env id
  | global && internal
  = return (occ_env, localiseName name)

  | global && external
  = return (occ_env, name)

  | local && internal
  = do uniq <- takeUniqFromNameCache name_cache
       let new_local_name = occ' `seq` mkInternalName uniq occ' loc
       return (occ_env', new_local_name)

  | local && external
  = do new_external_name <- allocateGlobalBinder name_cache mod occ' loc
       return (occ_env', new_external_name)

  | otherwise
  = panic "tidyTopName"
  where
    !name = varName id
    external = isJust maybe_ref
    global = isExternalName name
    local = not global
    internal = not external
    !loc = nameSrcSpan name

    old_occ = nameOccName name
    new_occ | Just ref <- maybe_ref
            , ref /= id
            = mkOccName (occNameSpace old_occ) $
              let ref_str = occNameString (getOccName ref)
                  occ_str = occNameString old_occ
              in if isSystemName name
                 then ref_str
                 else ref_str ++ '_' : occ_str
            | otherwise
            = old_occ

    (occ_env', occ') = tidyOccName occ_env new_occ

{- *********************************************************************
*                                                                      *
            Step 2: top-level tidying
*                                                                      *
********************************************************************* -}

tidyTopBinds
  :: UnfoldEnv
  -> TidyOccEnv
  -> CoreProgram
  -> IO (CoreTidyEnv, CoreProgram)
tidyTopBinds unfold_env init_occ_env binds = do
  let result = tidy init_env binds
  seqBinds (snd result) `seq` return result
  where
    init_env = (init_occ_env, emptyVarEnv, emptyVarEnv, emptyVarEnv, emptyVarEnv, emptyVarEnv)

    tidy = mapAccumL (tidyTopBind unfold_env)

tidyTopBind
  :: UnfoldEnv
  -> CoreTidyEnv
  -> CoreBind
  -> (CoreTidyEnv, CoreBind)
tidyTopBind unfold_env (occ_env, ids1, tcvs, tvs, kcvs, kvs) (NonRec bndr rhs)
  = (tidy_env2, NonRec bndr' rhs')
  where
    (bndr', rhs') = tidyTopPair unfold_env tidy_env2 (bndr, rhs)
    ids2 = extendVarEnv ids1 bndr bndr'
    tidy_env2 = (occ_env, ids2, tcvs, tvs, kcvs, kvs)

tidyTopBind unfold_env (occ_env, ids1, tcvs, tvs, kcvs, kvs) (Rec prs)
  = (tidy_env2, Rec prs')
  where
    prs' = map (tidyTopPair unfold_env tidy_env2) prs
    ids2 = extendVarEnvList ids1 (map fst prs `zip` map fst prs')
    tidy_env2 = (occ_env, ids2, tcvs, tvs, kcvs, kvs)

tidyTopPair
  :: UnfoldEnv
  -> CoreTidyEnv
  -> (CoreId, CoreExpr)
  -> (CoreId, CoreExpr)
tidyTopPair unfold_env rhs_tidy_env (bndr, rhs)
  = (bndr1, rhs1)
  where
    Just (name', show_unfold) = lookupVarEnv unfold_env bndr
    bndr1 = mkGlobalId details name' ty' idinfo'
    details = idDetails bndr
    ty' = tidyTopType (varType bndr)
    rhs1 = tidyExpr rhs_tidy_env rhs
    idinfo' = tidyTopIdInfo rhs_tidy_env name' ty' rhs rhs1 (idInfo bndr) show_unfold

tidyTopIdInfo
  :: CoreTidyEnv
  -> Name
  -> CoreType
  -> CoreExpr
  -> CoreExpr
  -> IdInfo
  -> Bool
  -> IdInfo
tidyTopIdInfo rhs_tidy_env name rhs_ty orig_rhs tidy_rhs idinfo show_unfold
  | not is_external
  = vanillaIdInfo
    `setArityInfo` arity
    `setDmdSigInfo` final_sig
    `setUnfoldingInfo` minimal_unfold_info

  | otherwise
  = vanillaIdInfo
    `setArityInfo` arity
    `setDmdSigInfo` final_sig
    `setOccInfo` robust_occ_info
    `setInlinePragInfo` inlinePragInfo idinfo
    `setUnfoldingInfo` unfold_info

  where
    is_external = isExternalName name

    -- OccInfo
    robust_occ_info = zapFragileOcc (occInfo idinfo)

    -- Demand
    mb_bot_str = exprBotStrictness_maybe orig_rhs

    sig = dmdSigInfo idinfo
    final_sig
      | not (isNopSig sig)
      = warnPprTrace (_bottom_hidden sig) "tidyTopIdInfo" (ppr name) sig
      | Just (_, bot_str_sig) <- mb_bot_str
      = bot_str_sig
      | otherwise
      = nopSig

    _bottom_hidden id_sig
      = case mb_bot_str of
          Nothing -> False
          Just (arity, _) -> not (isDeadEndAppSig id_sig arity)

    -- Unfolding
    unf_info = realUnfoldingInfo idinfo
    !minimal_unfold_info = trimUnfolding unf_info

    !unfold_info
      | isCompulsoryUnfolding unf_info || show_unfold
      = tidyTopUnfolding rhs_tidy_env tidy_rhs unf_info
      | otherwise
      = minimal_unfold_info

    -- Arity
    arity = exprArity orig_rhs `min` typeArity rhs_ty

tidyTopUnfolding :: CoreTidyEnv -> CoreExpr -> Unfolding -> Unfolding
tidyTopUnfolding _ _ NoUnfolding = NoUnfolding
tidyTopUnfolding _ _ OtherCon{} = evaldUnfolding
tidyTopUnfolding tidy_env tidy_rhs unf@CoreUnfolding{ uf_tmpl = unf_rhs, uf_src = src }
  = unf { uf_tmpl = tidy_unf_rhs }
  where
    tidy_unf_rhs
      | isStableSource src
      = tidyExpr tidy_env unf_rhs
      | otherwise
      = occurAnalyzeExpr tidy_rhs
