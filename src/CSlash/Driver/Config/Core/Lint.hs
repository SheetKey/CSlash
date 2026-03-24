module CSlash.Driver.Config.Core.Lint where

import CSlash.Driver.Env
import CSlash.Driver.DynFlags
import CSlash.Driver.Config.Diagnostic

import CSlash.Core
import CSlash.Core.Lint
import CSlash.Core.Opt.Pipeline.Types
import CSlash.Core.Opt.Simplify ( SimplifyOpts(..) )
-- import CSlash.Core.Opt.Simplify.Env ( SimplMode(..) )
-- import CSlash.Core.Opt.Monad
-- import CSlash.Core.Coercion

import CSlash.Types.Basic ( CompilerPhase(..) )

import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic

endPassCsEnvIO :: CsEnv -> NamePprCtx -> CoreToDo -> CoreProgram -> IO ()
endPassCsEnvIO cs_env name_ppr_ctx pass binds = do
  let dflags = cs_dflags cs_env
  endPassIO (cs_logger cs_env)
            (initEndPassConfig dflags name_ppr_ctx pass)
            binds

initEndPassConfig :: DynFlags -> NamePprCtx -> CoreToDo -> EndPassConfig
initEndPassConfig dflags name_ppr_ctx pass = EndPassConfig
  { ep_dumpCoreSizes = not (gopt Opt_SuppressCoreSizes dflags)
  , ep_lintPassResult = if gopt Opt_DoCoreLinting dflags
                        then Just $ initLintPassResultConfig dflags pass
                        else Nothing
  , ep_namePprCtx = name_ppr_ctx
  , ep_dumpFlag = coreDumpFlag pass
  , ep_prettyPass = ppr pass
  , ep_passDetails = pprPassDetails pass
  }

coreDumpFlag :: CoreToDo -> Maybe DumpFlag
coreDumpFlag CoreDoSimplify{} = Just Opt_D_verbose_core2core
coreDumpFlag CoreDesugar = Just Opt_D_dump_ds_preopt
coreDumpFlag CoreDesugarOpt = Just Opt_D_dump_ds
coreDumpFlag CoreTidy = Just Opt_D_dump_simpl
coreDumpFlag CorePrep = Just Opt_D_dump_prep

initLintPassResultConfig :: DynFlags -> CoreToDo -> LintPassResultConfig
initLintPassResultConfig dflags pass = LintPassResultConfig
  { lpr_diagOpts = initDiagOpts dflags
  , lpr_platform = targetPlatform dflags
  , lpr_makeLintFlags = perPassFlags dflags pass
  , lpr_showLintWarnings = showLintWarnings pass
  , lpr_passPpr = panic "ppr pass"
  , lpr_localsInScope = panic "extra_vars"
  }

showLintWarnings :: CoreToDo -> Bool
showLintWarnings (CoreDoSimplify {}) = panic "showLintWarnings"
showLintWarnings _ = True

perPassFlags :: DynFlags -> CoreToDo -> LintFlags
perPassFlags dflags pass = (defaultLintFlags dflags)
  { lf_check_global_ids = check_globals
  , lf_check_inline_loop_breakers = check_lbs
  }
  where
    check_globals = case pass of
                      CoreTidy -> False
                      CorePrep -> False
                      _ -> True

    check_lbs = case pass of
                  CoreDesugar -> False
                  CoreDesugarOpt -> False
                  _ -> True

defaultLintFlags :: DynFlags -> LintFlags
defaultLintFlags dflags = LF { lf_check_global_ids = False
                             , lf_check_inline_loop_breakers = True
                             , lf_report_unsat_syns = True
                             }
