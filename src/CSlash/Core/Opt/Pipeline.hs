{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Opt.Pipeline where

import CSlash.Driver.DynFlags
import CSlash.Driver.Env
import CSlash.Driver.Config.Core.Lint ( endPass )
-- import GHC.Driver.Config.Core.Opt.LiberateCase ( initLiberateCaseOpts )
import CSlash.Driver.Config.Core.Opt.Simplify
  ( initSimplifyOpts, initSimplMode, initGentleSimplMode )
-- import GHC.Driver.Config.Core.Opt.WorkWrap ( initWorkWrapOpts )
-- import GHC.Driver.Config.Core.Rules ( initRuleOpts )
import CSlash.Platform.Ways  ( hasWay, Way(WayProf) )

import CSlash.Core
-- import GHC.Core.Opt.CSE  ( cseProgram )
-- import GHC.Core.Rules   ( RuleBase, mkRuleBase, ruleCheckProgram, getRules )
import CSlash.Core.Ppr     ( pprCoreBindings )
import CSlash.Core.Utils   ( dumpIdInfoOfProgram )
-- import CSlash.Core.Lint    ( lintAnnots )
-- import CSlash.Core.Opt.Simplify ( simplifyExpr, simplifyPgm )
-- import GHC.Core.Opt.Simplify.Monad
import CSlash.Core.Opt.Monad
import CSlash.Core.Opt.Stats
import CSlash.Core.Opt.Pipeline.Types
-- import GHC.Core.Opt.FloatIn      ( floatInwards )
import CSlash.Core.Opt.FloatOut     ( floatOutwards )
-- import GHC.Core.Opt.LiberateCase ( liberateCase )
-- import GHC.Core.Opt.StaticArgs   ( doStaticArgs )
import CSlash.Core.Opt.Specialize   ( specProgram)
-- import GHC.Core.Opt.SpecConstr   ( specConstrProgram)
import CSlash.Core.Opt.DmdAnal
-- import GHC.Core.Opt.CprAnal      ( cprAnalProgram )
-- import GHC.Core.Opt.CallArity    ( callArityAnalProgram )
-- import GHC.Core.Opt.Exitify      ( exitifyProgram )
-- import GHC.Core.Opt.WorkWrap     ( wwTopBinds )
-- import GHC.Core.Opt.CallerCC     ( addCallerCostCentres )
-- import GHC.Core.LateCC.TopLevelBinds (topLevelBindsCCMG)
import CSlash.Core.Seq (seqBinds)

import CSlash.Utils.Error  ( withTiming )
import CSlash.Utils.Logger as Logger
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Monad

import CSlash.Unit.Module.ModGuts

import CSlash.Types.Var.Id.Info
import CSlash.Types.Basic
import CSlash.Types.Demand ( zapDmdEnvSig )
import CSlash.Types.Name.Ppr
import CSlash.Types.Var
import CSlash.Types.Unique
import CSlash.Types.Unique.Supply

import Control.Monad
import CSlash.Unit.Module

{- *********************************************************************
*                                                                      *
          The driver for the simplifier
*                                                                      *
********************************************************************* -}

core2core :: CsEnv -> ModGuts -> IO ModGuts
core2core cs_env guts@(ModGuts { mg_module = mod
                               , mg_loc = loc
                               , mg_rdr_env = rdr_env })
  = do let builtin_passes = getCoreToDo dflags
           uniq_tag = 's'
       (guts2, stats) <- runCoreM cs_env uniq_tag mod name_ppr_ctx loc $ do
         cs_env' <- getCsEnv
         runCorePasses builtin_passes guts

       Logger.putDumpFileMaybe logger Opt_D_dump_simpl_stats
         "Grand totoal simplifier statistics"
         FormatText
         (pprSimplCount stats)

       return guts2

  where
    dflags = cs_dflags cs_env
    logger = cs_logger cs_env
    name_ppr_ctx = mkNamePprCtx (cs_unit_env cs_env) rdr_env

{- *********************************************************************
*                                                                      *
           Generating the main optimisation pipeline
*                                                                      *
********************************************************************* -}

getCoreToDo :: DynFlags -> [CoreToDo]
getCoreToDo dflags = flatten_todos core_todo
  where
    phases = simplPhases dflags
    max_iter = maxSimplIterations dflags
    const_fold = gopt Opt_CoreConstantFolding dflags
    call_arity = gopt Opt_CallArity dflags
    exitification = gopt Opt_Exitification dflags
    strictness = True -- TODO: gopt Opt_Strictness dflags
    do_specialize = gopt Opt_Specialise dflags
    do_float_in = gopt Opt_FloatIn dflags
    cse = gopt Opt_CSE dflags
    spec_constr = gopt Opt_SpecConstr dflags
    liberate_case = gopt Opt_LiberateCase dflags
    late_dmd_anal = gopt Opt_LateDmdAnal dflags
    late_specialize = gopt Opt_LateSpecialise dflags
    static_args = gopt Opt_StaticArgumentTransformation dflags
    profiling = ways dflags `hasWay` WayProf

    do_presimplify = do_specialize
    do_simpl3 = const_fold

    maybe_strictness_before (Phase phase)
      | phase `elem` [] {-TODO: strictnessBefore dflags-} = CoreDoDemand 
    maybe_strictness_before _ = CoreDoNothing

    simpl_phase phase name iter
      = CoreDoPasses
        [ maybe_strictness_before phase
        , CoreDoSimplify $ initSimplifyOpts dflags iter
          (initSimplMode dflags phase name)
        ]

    simplify name = simpl_phase FinalPhase name max_iter

    simpl_gently
      = CoreDoSimplify $ initSimplifyOpts dflags max_iter (initGentleSimplMode dflags)

    dmd_cpr_ww = [CoreDoDemand]

    demand_analyzer = CoreDoPasses (dmd_cpr_ww ++ [simplify "post-demand"])

    add_caller_ccs = runWhen (profiling && not (null $ callerCcFilters dflags)) CoreAddCallerCcs

    add_late_ccs = runWhen (profiling && gopt Opt_ProfLateInlineCcs dflags) $ CoreAddLateCcs

    core_todo =
      [ runWhen static_args (CoreDoPasses [ simpl_gently, CoreDoStaticArgs ])
      , runWhen do_presimplify simpl_gently
      , runWhen do_specialize CoreDoSpecializing
      , CoreDoFloatOutwards $ FloatOutSwitches
        { floatOutAllLambdas = False
        , floatOutConstants = True
        , floatOutOverSatApps = False
        , floatToTopLevelOnly = False
        , floatJoinsToTop = False
        }
      , runWhen do_simpl3
        (CoreDoPasses $ [ simpl_phase (Phase phase) "main" max_iter
                        | phase <- [phases, phases-1..1] ]
          ++ [simpl_phase (Phase 0) "main" (max max_iter 3) ])
      , runWhen do_float_in CoreDoFloatInwards
      , runWhen call_arity $ CoreDoPasses [ CoreDoCallArity, simplify "post-call-arity" ]
      , runWhen strictness demand_analyzer
      , runWhen exitification CoreDoExitify
      , CoreDoFloatOutwards $ FloatOutSwitches
        { floatOutAllLambdas = True
        , floatOutConstants = True
        , floatOutOverSatApps = True
        , floatToTopLevelOnly = False
        , floatJoinsToTop = True
        }
      , runWhen cse CoreCSE
      , runWhen do_float_in CoreDoFloatInwards
      , simplify "final"
        -- -O2
      , runWhen liberate_case $ CoreDoPasses
        [ CoreLiberateCase, simplify "post-liberate-case" ]
      , runWhen spec_constr $ CoreDoPasses
        [ CoreDoSpecConstr, simplify "post-spec-constr" ]
      , runWhen late_specialize $ CoreDoPasses
        [ CoreDoSpecializing, simplify "post-late-spec" ]
      , runWhen ((liberate_case || spec_constr) && cse) $ CoreDoPasses
        [ CoreCSE, simplify "post-final-cse" ]
        -- End of -O2
      , runWhen late_dmd_anal $ CoreDoPasses
        (dmd_cpr_ww ++ [simplify "post-late-ww"])
      , CoreDoDemand
      , add_caller_ccs
      , add_late_ccs
      ]

    flatten_todos [] = []
    flatten_todos (CoreDoNothing : rest) = flatten_todos rest
    flatten_todos (CoreDoPasses passes : rest) = flatten_todos passes ++ flatten_todos rest
    flatten_todos (todo : rest) = todo : flatten_todos rest

runWhen :: Bool -> CoreToDo -> CoreToDo
runWhen True do_this = do_this
runWhen False _ = CoreDoNothing

{- *********************************************************************
*                                                                      *
                  The CoreToDo interpreter
*                                                                      *
********************************************************************* -}

runCorePasses :: [CoreToDo] -> ModGuts -> CoreM ModGuts
runCorePasses passes guts = foldM do_pass guts passes
  where
    do_pass guts CoreDoNothing = return guts
    do_pass guts (CoreDoPasses ps) = runCorePasses ps guts
    do_pass guts pass = do
      logger <- getLogger
      withTiming logger (ppr pass <+> brackets (ppr mod)) (const ()) $ do
        guts' <- doCorePass pass guts
        endPass pass (mg_binds guts')
        return guts'

    mod = mg_module guts

doCorePass :: CoreToDo -> ModGuts -> CoreM ModGuts
doCorePass pass guts = do
  logger <- getLogger
  cs_env <- getCsEnv
  dflags <- getDynFlags
  us <- getUniqueSupplyM
  let platform = targetPlatform dflags
      updateBinds f = return $ guts { mg_binds = f (mg_binds guts) }
      updateBindsM f = f (mg_binds guts) >>= \b' -> return $ guts { mg_binds = b' }
      !rdr_env = mg_rdr_env guts
      name_ppr_ctx = mkNamePprCtx (cs_unit_env cs_env) rdr_env

  case pass of 
    CoreDoSimplify opts -> {-# SCC "Simplify" #-}
                           panic "liftIOWithCount $ simplifyPgm logger (cs_unit_env cs_env)"

    CoreCSE -> {-# SCC "CommonSubExpr" #-}
               panic "updateBinds cseProgram"

    CoreLiberateCase -> {-# SCC "LiberateCase" #-}
                        panic "updateBinds (liberateCase (initLiberateCaseOpts dflags))"

    CoreDoFloatInwards -> {-# SCC "FloatInwards" #-}
                          panic "updateBinds (floatInwards platform)"

    CoreDoFloatOutwards f -> {-# SCC "FloatOutwards" #-}
                             updateBindsM (liftIO . floatOutwards logger f us)

    CoreDoStaticArgs -> {-# SCC "StaticArgs" #-}
                        panic "updateBinds (doStaticArgs us)"

    CoreDoCallArity -> {-# SCC "CallArity" #-}
                       panic "updateBinds callArityAnalProgram"

    CoreDoExitify -> {-# SCC "Exitify" #-}
                     panic "updateBinds exitifyProgram"

    CoreDoDemand -> {-# SCC "DmdAnal" #-}
                    updateBindsM (liftIO . dmdAnal logger dflags)

    CoreDoSpecializing -> {-# SCC "Specialize" #-}
                          specProgram guts

    CoreDoSpecConstr -> {-# SCC "SpecConstr" #-}
                        panic "specConstrProgram" guts

    CoreAddCallerCcs -> {-# SCC "AddCallerCcs" #-}
                        panic "addCallerCostCenters guts"

    CoreAddLateCcs -> {-# SCC "AddLateCcs" #-}
                      panic "topLevelBindsCCMG guts"

    CoreDoNothing -> return guts
    CoreDoPasses passes -> runCorePasses passes guts

    CoreDesugar -> pprPanic "doCorePass" (ppr pass)
    CoreDesugarOpt -> pprPanic "doCorePass" (ppr pass)
    CoreTidy -> pprPanic "doCorePass" (ppr pass)
    CorePrep -> pprPanic "doCorePass" (ppr pass)

{- *********************************************************************
*                                                                      *
          Core pass combinators
*                                                                      *
********************************************************************* -}

dmdAnal :: Logger -> DynFlags -> CoreProgram -> IO CoreProgram
dmdAnal logger dflags binds = do
  let binds_plus_dmds = dmdAnalProgram binds
  Logger.putDumpFileMaybe logger Opt_D_dump_dmd_signatures "Demand signatures" FormatText
    $ dumpIdInfoOfProgram (hasPprDebug dflags) (ppr . zapDmdEnvSig . dmdSigInfo) binds_plus_dmds

  seqBinds binds_plus_dmds `seq` return binds_plus_dmds
