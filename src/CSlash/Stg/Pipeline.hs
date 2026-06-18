{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module CSlash.Stg.Pipeline
  ( StgPipelineOpts(..)
  , StgToDo(..)
  , stg2stg
  ) where

import CSlash.Driver.Flags
import CSlash.Core

import CSlash.Stg.Syntax

-- import GHC.Stg.Lint     ( lintStgTopBindings )
-- import GHC.Stg.Stats    ( showStgStats )
import CSlash.Stg.FVs      ( depSortWithAnnotStgPgm )
import CSlash.Stg.Unarise  ( unarise )
-- import GHC.Stg.BcPrep   ( bcPrep )
import CSlash.Stg.Lift     ( StgLiftConfig, stgLiftLams )
import CSlash.Unit.Module ( Module )

import CSlash.Core.DataCon (DataCon)

import CSlash.Utils.Error
import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Types.Unique.Supply
import CSlash.Utils.Outputable
import CSlash.Utils.Logger
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Reader
import CSlash.Platform (Platform)
-- import GHC.Stg.InferTags (inferTags)
-- import GHC.Stg.InferTags.TagSig ( StgCgInfos )

import CSlash.Utils.Panic

data StgPipelineOpts = StgPipelineOpts
  { stgPipeline_phases :: ![StgToDo]
  , stgPipeline_lint :: !(Maybe DiagOpts)
  , stgPipeline_pprOpts :: !StgPprOpts
  , stgPlatform :: !Platform
  , stgPipeline_allowTopLevelConApp :: Module -> CoreDataCon -> [StgArg] -> Bool
  }

newtype StgM a = StgM { _unStgM :: ReaderT Char IO a }
  deriving (Functor, Applicative, Monad, MonadIO)

instance MonadUnique StgM where
  getUniqueSupplyM = StgM $ do
    tag <- ask
    liftIO $! mkSplitUniqSupply tag

  getUniqueM = StgM $ do
    tag <- ask
    liftIO $! uniqFromTag tag

runStgM :: Char -> StgM a -> IO a
runStgM mask (StgM m) = runReaderT m mask

stg2stg
  :: Logger
  -> StgPipelineOpts
  -> Module
  -> [StgTopBinding]
  -> IO [(CgStgTopBinding, CoreIdSet)]
stg2stg logger opts this_mod binds = do
  dump_when Opt_D_dump_stg_from_core "Initial STG:" binds
  stg_linter False "StgFromCore" binds
  showPass logger "Stg2Stg"
  binds' <- runStgM 'g' $
    foldM (do_stg_pass this_mod) binds (stgPipeline_phases opts)

  let (cg_binds, imp_fvs) = unzip (depSortWithAnnotStgPgm this_mod binds')
  stg_linter False "StgCodeGen" cg_binds
  pure (zip cg_binds imp_fvs)
  where
    stg_linter
      :: (BinderP a ~ CoreId, OutputablePass a)
      => Bool -> String -> [GenStgTopBinding a] -> IO ()
    stg_linter unarised
      | Just diap_opts <- stgPipeline_lint opts
      = panic "lintStgTopBindings"

      | otherwise
      = \_ _ -> return ()

    do_stg_pass :: Module -> [StgTopBinding] -> StgToDo -> StgM [StgTopBinding]
    do_stg_pass this_mod binds to_do
      = case to_do of
          StgDoNothing -> return binds

          StgStats -> panic "StgStats"

          StgLiftLams cfg -> do
            us <- getUniqueSupplyM
            let binds' = {-# SCC "StgLiftLams" #-} stgLiftLams this_mod cfg us binds
            end_pass "StgLiftLams" binds'

          StgUnarise -> do
            us <- getUniqueSupplyM
            liftIO (stg_linter False "Pre-unarise" binds)
            let binds' = {-# SCC "StgUnarise" #-}
                         unarise us (stgPipeline_allowTopLevelConApp opts this_mod) binds
            liftIO (dump_when Opt_D_dump_stg_unarised "Unarised STG:" binds')
            liftIO (stg_linter True "Unarise" binds')
            return binds'

    ppr_opts = stgPipeline_pprOpts opts
    dump_when flag header binds
      = putDumpFileMaybe logger flag header FormatSTG (pprStgTopBindings ppr_opts binds)

    end_pass what binds2
      = liftIO $ do
          putDumpFileMaybe logger Opt_D_verbose_stg2stg what
            FormatSTG (vcat (map (pprStgTopBinding ppr_opts) binds2))
          stg_linter False what binds2
          return binds2

data StgToDo
  = StgLiftLams StgLiftConfig
  | StgStats
  | StgUnarise
  | StgDoNothing
  deriving (Show, Read, Eq, Ord)
