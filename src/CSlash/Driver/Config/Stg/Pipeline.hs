{-# LANGUAGE BangPatterns #-}

module CSlash.Driver.Config.Stg.Pipeline (initStgPipelineOpts) where

import Control.Monad (guard)

import CSlash.Stg.Pipeline
import CSlash.Stg.Utils

import CSlash.Driver.Config.Diagnostic
import CSlash.Driver.Config.Stg.Lift
import CSlash.Driver.Config.Stg.Ppr
import CSlash.Driver.DynFlags

initStgPipelineOpts :: DynFlags -> StgPipelineOpts
initStgPipelineOpts dflags =
  let !platform = targetPlatform dflags
      !ext_dyn_refs = gopt Opt_ExternalDynamicRefs dflags
  in StgPipelineOpts
     { stgPipeline_lint = do
         guard $ gopt Opt_DoStgLinting dflags
         Just $ initDiagOpts dflags
     , stgPipeline_pprOpts = initStgPprOpts dflags
     , stgPipeline_phases = getStgToDo dflags
     , stgPlatform = platform
     , stgPipeline_allowTopLevelConApp = allowTopLevelConApp platform ext_dyn_refs
     }

getStgToDo :: DynFlags -> [StgToDo]
getStgToDo dflags =
  filter (/= StgDoNothing)
  [ StgUnarise
  , optional Opt_StgCSE StgCSE
  , StgLiftLams $ initStgLiftConfig dflags
  , optional Opt_StgStats StgStats
  ]
  where optional opt = runWhen (gopt opt dflags)

runWhen :: Bool -> StgToDo -> StgToDo
runWhen True todo = todo
runWhen _ _ = StgDoNothing
