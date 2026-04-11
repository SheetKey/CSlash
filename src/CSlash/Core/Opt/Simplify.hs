module CSlash.Core.Opt.Simplify where

import CSlash.Cs.Pass

import CSlash.Driver.Flags

import CSlash.Core
import CSlash.Core.Rules
import CSlash.Core.Ppr     ( pprCoreBindings, pprCoreExpr )
-- import CSlash.Core.Opt.OccurAnal ( occurAnalysePgm, occurAnalyseExpr )
-- import CSlash.Core.Stats   ( coreBindsSize, coreBindsStats, exprSize )
-- import CSlash.Core.Utils   ( mkTicks, stripTicksTop )
import CSlash.Core.Lint    ( LintPassResultConfig, dumpPassResult, lintPassResult )
import CSlash.Core.Opt.Simplify.Iteration ( simplTopBinds, simplExpr, simplImpRules )
import CSlash.Core.Opt.Simplify.Inline ( activeUnfolding )
import CSlash.Core.Opt.Simplify.Env
import CSlash.Core.Opt.Simplify.Monad
-- import CSlash.Core.Opt.Stats ( simplCountN )

import CSlash.Utils.Error  ( withTiming )
import CSlash.Utils.Logger as Logger
import CSlash.Utils.Outputable
import CSlash.Utils.Constants (debugIsOn)

-- import CSlash.Unit.Env ( UnitEnv, ueEPS )
import CSlash.Unit.External
import CSlash.Unit.Module.ModGuts

import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Basic
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.Tickish
import CSlash.Types.Unique.FM

import Control.Monad
import Data.Foldable ( for_ )

{- *********************************************************************
*                                                                      *
        Gentle simplification
*                                                                      *
********************************************************************* -}

data SimplifyExprOpts = SimplifyExprOpts
  { se_mode :: !SimplMode
  , se_top_env_cfg :: !TopEnvConfig
  }

{- *********************************************************************
*                                                                      *
            The driver for the simplifier
*                                                                      *
********************************************************************* -}

data SimplifyOpts = SimplifyOpts
  { so_dump_core_sizes :: !Bool
  , so_iterations :: !Int
  , so_mode :: !SimplMode
  , so_pass_result_cfg :: !(Maybe LintPassResultConfig)
  , so_hpt_rules :: !RuleBase
  , so_top_env_cfg :: !TopEnvConfig
  }

simplifyPgm
  :: Logger
  -> UnitEnv
  -> NamePprCtx
  -> SimplifyOpts
  -> ModGuts
  -> IO (SimplCount, ModGuts)
simplifyPgm logger unit_env name_ppr_ctx opts guts@(ModGuts { mg_module = this_mod
                                                            , mg_binds = binds
                                                            , mg_rules = local_rules })
  = do (termination_msg, it_count, counts_out, guts')
         <- do_iteration 1 [] binds local_rules

       panic "simplifyPgm unfinished"

  where
    dump_core_sizes = so_dump_core_sizes opts
    mode = so_mode opts
    max_iterations = so_iterations opts
    top_env_cfg = so_top_env_cfg opts
    active_rule = activeRule mode
    active_unf = activeUnfolding mode

    !guts_no_binds = guts { mg_binds = [], mg_rules = [] }

    hpt_rule_env :: RuleEnv
    hpt_rule_env = mkRuleEnv guts emptyRuleBase (so_hpt_rules opts)

    do_iteration
      :: Int
      -> [SimplCount]
      -> CoreProgram
      -> [CoreRule]
      -> IO (String, Int, SimplCount, ModGuts)
    do_iteration iteration_no counts_so_far binds local_rules
      | iteration_no > max_iterations
      = warnPprTrace (debugIsOn && (max_iterations > 2))
        "Simplifier bailing out"
        (hang (ppr this_mod <> text ", after"
               <+> int max_iterations <+> text "iterations"
               <+> (brackets $ hsep $ punctuate comma $
                    map (int . simplCountN) (reverse counts_so_far)))
          2 (text "Size =" <+> ppr (coreBindsStats binds))) $

        return ( "Simplifier bailed out"
               , iteration_no - 1
               , totalize counts_so_far
               , guts_no_binds { mg_binds = binds, mg_rules = local_rules } )

      | let sz = coreBindsSize binds
      , () <- sz `seq` ()
      = do let tagged_binds = {-# SCC "OccAnal" #-}
                              occurAnaluzePgm this_mod active_unf active_rule local_rules binds

           Logger.putDumpFileMaybe logger Opt_D_dump_occur_anal "Occurrence analysis"
             FormatCore (pprCoreBindings tagged_binds)

           eps <- ueEPS unit_env
           let !base_rule_env = updLocalRules hpt_rule_env local_rules

               read_eps_rules :: IO PackageRuleBase
               read_eps_rules = eps_rule_base <$> ueEPS unit_env

               read_rule_env :: IO RuleEnv
               read_rule_env = updExternalPackageRules base_rule_env <$> read_eps_rules

               simpl_env = mkSimplEnv mode

           ((binds1, rules1), counts1) <-
             initSimpl logger read_rule_env top_env_cfg sz $ do
               (floats, env1) <- {-# SCC "SimplTopBinds" #-} simplTopBinds simpl_env tagged_binds

               rules1 <- simplImpRules env1 local_rules

               return (getTopFloatBinds floats, rules1)

           if isZeroSimplCount counts1
             then return ( "Simplifier reached fixed point"
                         , iteration_no
                         , totalize (counts1 : counts_so_far)
                         , guts_no_binds { mg_binds = binds1, mg_rules = rules1 } )

             else do let binds2 = {-# SCC "ZapInd" #-} shortOutIndirections binds1

                     dump_end_iteration logger dump_cor_sizes name_ppr_ctx
                       iteration_no counts1 binds2 rules1

                     for_ (so_pass_result_cfg opts) $ \pass_result_cfg ->
                       lintPassResult logger pass_result_cfg binds2

                     do_iterations (iteration_no + 1) (counts1 : counts_so_fat) binds2 rules1
      where
        totalize :: [SimplCount] -> SimplCount
        totalize = foldr (\c acc -> acc `plusSimplCount` c)
                         (zeroSimplCount $ logHasDumpFlag logger Opt_D_dump_simpl_stats)

dump_end_iteration
  :: Logger
  -> Bool
  -> NamePprCtx
  -> Int
  -> SimplCount
  -> CoreProgram
  -> [CoreRule]
  -> IO ()
dump_end_iteration logger dump_core_sizes name_ppr_ctx iteration_no counts binds rules
  = dumpPassResult logger dump_core_sizes name_ppr_ctx mb_flag hdr ppr_counts binds rules
  where
    mb_flag | logHasDumpFlag logger Opt_D_dump_simpl_iterations = Just Opt_D_dump_simpl_iterations
            | otherwise = Nothing

    hdr = "Simplifier iteration=" ++ show iteration_no
    pp_counts = vcat [ text "---- Simplifier counts for" <+> text hdr
                     , pprSimplCount counts
                     , text "---- End of simplifier counts for" <+> text hdr ]

{- *********************************************************************
*                                                                      *
        Shorting out indirections
*                                                                      *
********************************************************************* -}

type IndEnv = IdEnv Zk (CoreId, [CoreTickish])

shortOutIndirections :: CoreProgram -> CoreProgram
shortOutIndirections binds
  | isEmptyVarEnv ind_env = binds
  | no_need_to_flatten = binds'
  | otherwise = [Rec (flattenBinds binds')]
  where
    ind_env = makeIndEnv binds

    exp_ids = map fst $ nonDetEltsUFM ind_env
    exp_id_set = mkVarSet exp_ids
    no_need_to_flatten = all (null . ruleInfoRule . idSpecialization) exp_ids

    binds' = concatMap zap binds

    zap (NonRec bndr rhs) = [NonRec b r | (b, r) <- zapPair (bndr, rhs)]
    zap (Rec pairs) = [Rec (concatMap zapPair pairs)]

    zapPair (bndr, rhs)
      | bndr `elemVarSet` exp_id_set
      = []
      | Just (exp_id, ticks) <- lookupVarEnv ind_env bndr
      , (exp_id', lcl_id') <- transferIdInfo exp_id bndr
      = [ (exp_id', mkTicks ticks rhs)
        , (lcl_id', Var exp_id' ) ]
      | otherwise
      = [(bndr, rhs)]

makeIndEnv :: [CoreBind] -> IndEnv
makeIndEnv binds = foldl' add_bind emptyVarEnv binds
  where
    add_bind :: IndEnv -> CoreBind -> IndEnv
    add_bind env (NonRec exported_id rhs) = add_pair env (exported_id, rhs)
    add_bind env (Rec pairs) = foldrl' add_pair env pairs

    add_pair :: IndEnv -> (CoreId, CoreExpr) -> IndEnv
    add_pair env (exported_id, exported)
      | (ticks, Var local_id) <- stripTicksTop tickishFloatable exported
      , shortMeOut env exported_id local_id
      = extendVarenv env local_id (exported_id, ticks)
    add_pair env _ = env

shortMeOut :: IndEnv -> CoreId -> CoreId -> Bool
shortMeOut ind_env exported_id local_id
  = if isExportedId exported_id &&
       isLocalId local_id &&
       not (isExportedId local_id) &&
       not (local_id `elemVarEnv` ind_env)
    then if hasShortableIdInfo exported_id
         then True
         else warnPprTrace True "Not shorting out" (ppr exported_id) False
    else False

hasShortableIdInfo :: CoreId -> Bool
hasShortableIdInfo id
  = isEmptyRuleInfo (ruleInfo info) &&
    isDefaultInlinePragma (inlinePragInfo info) &&
    not (isStableUnfolding (realUnfoldingInfo info))
  where
    info = idInfo id

transferIdInfo :: CoreId -> CoreId -> (CoreId, CoreId)
transferIdInfo exported_id local_id
  = ( modifyIfInfo transfer exported_id
    , modifyIdInfo zap_info local_id )
  where
    local_info = idInfo local_id
    transfer exp_info = exp_info `setDmdSigInfo` dmdSigInfo local_info
                                 `setUnfoldingInfo` realUnfoldingInfo loacl_info
                                 `setInlinePragInfo` inlinePragInfo local_info
                                 `setRuleInfo` addRuleInfo (ruleInfo exp_info) new_info

    new_info = setRuleInfoHead (varName exported_id) (ruleInfo local_info)

    zap_info lcl_info = lcl_info `setInlinePragInfo` defaultInlinePragma
                                 `setUnfoldingInfo` noUnfolding
