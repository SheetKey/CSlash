module CSlash.Driver.Config.Core.Opt.Simplify where

import CSlash.Core.Rules (RuleBase)
import CSlash.Core.Opt.Pipeline.Types ( CoreToDo(..) )
import CSlash.Core.Opt.Simplify ( {-SimplifyExprOpts(..), -}SimplifyOpts(..) )
import CSlash.Core.Opt.Simplify.Env ( FloatEnable(..), SimplMode(..) )
import CSlash.Core.Opt.Simplify.Monad ( TopEnvConfig(..) )

import CSlash.Driver.Config ( initOptCoercionOpts )
import CSlash.Driver.Config.Core.Lint ( initLintPassResultConfig )
import CSlash.Driver.Config.Core.Rules ( initRuleOpts )
import CSlash.Driver.Config.Core.Opt.Arity ( initArityOpts )
import CSlash.Driver.DynFlags ( DynFlags(..), GeneralFlag(..), gopt )

import CSlash.Types.Basic ( CompilerPhase(..) )

import CSlash.Utils.Panic

initSimplifyOpts :: DynFlags -> Int -> SimplMode -> RuleBase -> SimplifyOpts
initSimplifyOpts dflags iterations mode hpt_rule_base
  = let opts = SimplifyOpts
          { so_dump_core_sizes = not $ gopt Opt_SuppressCoreSizes dflags
          , so_iterations = iterations
          , so_mode = mode
          , so_pass_result_cfg = if gopt Opt_DoCoreLinting dflags
                                 then Just $ initLintPassResultConfig dflags (CoreDoSimplify opts)
                                 else Nothing
          , so_hpt_rules = hpt_rule_base
          , so_top_env_cfg = TopEnvConfig { te_history_size = historySize dflags
                                          , te_tick_factor = simplTickFactor dflags }
          }
    in opts

initSimplMode :: DynFlags -> CompilerPhase -> String -> SimplMode
initSimplMode dflags phase name = SimplMode
  { sm_phase = phase
  , sm_names = [name]
  , sm_rules = gopt Opt_EnableRewriteRules dflags
  , sm_inline = True
  , sm_eta_expand = gopt Opt_DoLambdaEtaExpansion dflags
  , sm_cast_swizzle = True
  , sm_uf_opts = unfoldingOpts dflags
  , sm_case_case = True
  , sm_pre_inline = gopt Opt_SimplPreInlining dflags
  , sm_float_enable = floatEnable dflags
  , sm_do_eta_reduction = gopt Opt_DoEtaReduction dflags
  , sm_arity_opts = initArityOpts dflags
  , sm_rule_opts = initRuleOpts dflags
  , sm_case_folding = gopt Opt_CaseFolding dflags
  , sm_case_merge = gopt Opt_CaseMerge dflags
  , sm_co_opt_opts = initOptCoercionOpts dflags
  }

initGentleSimplMode :: DynFlags -> SimplMode
initGentleSimplMode dflags = (initSimplMode dflags InitialPhase "Gentle")
  { sm_case_case = False }

floatEnable :: DynFlags -> FloatEnable
floatEnable dflags = case (gopt Opt_LocalFloatOut dflags, gopt Opt_LocalFloatOutTopLevel dflags) of
  (True, True) -> FloatEnabled
  (True, False) -> FloatNestedOnly
  (False, _) -> FloatDisabled
