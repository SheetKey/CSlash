{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}

module CSlash.Driver.Pipeline where

import CSlash.Platform

import CSlash.Utils.Monad ( MonadIO(liftIO), mapMaybeM )

import CSlash.Driver.Main
import CSlash.Driver.Env hiding ( Cs )
import CSlash.Driver.Errors
import CSlash.Driver.Errors.Types
import CSlash.Driver.Pipeline.Monad
import CSlash.Driver.Config.Diagnostic
-- import GHC.Driver.Config.StgToJS
import CSlash.Driver.Phases
import CSlash.Driver.Pipeline.Execute
import CSlash.Driver.Pipeline.Phases
import CSlash.Driver.Session
import CSlash.Driver.Backend
import CSlash.Driver.Ppr
-- import GHC.Driver.Hooks

import CSlash.Platform.Ways

import CSlash.SysTools
-- import GHC.SysTools.Cpp
import CSlash.Utils.TmpFs

-- import GHC.Linker.ExtraObj
import CSlash.Linker.Static
-- import GHC.Linker.Static.Utils
import CSlash.Linker.Types

-- import GHC.StgToJS.Linker.Linker

import CSlash.Utils.Outputable
import CSlash.Utils.Error
import CSlash.Utils.Panic
import CSlash.Utils.Misc
import CSlash.Utils.Exception as Exception
import CSlash.Utils.Logger

-- import qualified GHC.LanguageExtensions as LangExt

import CSlash.Data.FastString     ( mkFastString )
import CSlash.Data.StringBuffer   ( hPutStringBuffer )
import CSlash.Data.Maybe          ( expectJust )

import CSlash.Iface.Make          ( mkFullIface )
-- import GHC.Runtime.Loader      ( initializePlugins )

import CSlash.Types.Basic       ( SuccessFlag(..), ForeignSrcLang(..) )
import CSlash.Types.Error       ( singleMessage, getMessages, mkSimpleUnknownDiagnostic, defaultDiagnosticOpts )
import CSlash.Types.Target
import CSlash.Types.SrcLoc
import CSlash.Types.SourceFile
import CSlash.Types.SourceError

import CSlash.Unit
import CSlash.Unit.Env
import CSlash.Unit.Finder
--import GHC.Unit.State
import CSlash.Unit.Module.ModSummary
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.Deps
import CSlash.Unit.Home.ModInfo

import System.Directory
import System.FilePath
import System.IO
import Control.Monad
import qualified Control.Monad.Catch as MC (handle)
import Data.Maybe
import qualified Data.Set as Set

import Data.Time        ( getCurrentTime )
-- import CSlash.Iface.Recomp
import CSlash.Types.Unique.DSet

type P m = TPipelineClass TPhase m

-- ---------------------------------------------------------------------------
-- Pre-process

-- ---------------------------------------------------------------------------
-- Compile

-- ---------------------------------------------------------------------------
-- Link

-- -----------------------------------------------------------------------------
-- Compile files in one-shot mode.

oneShot :: CsEnv -> StopPhase -> [(String, Maybe Phase) ] -> IO ()
oneShot cs_env stop_phase srcs = do
  o_files <- mapMaybeM (compileFile cs_env stop_phase) srcs
  case stop_phase of
    NoStop -> doLink cs_env o_files

compileFile :: CsEnv -> StopPhase -> (FilePath, Maybe Phase) -> IO (Maybe FilePath)
compileFile cs_env stop_phase (src, mb_phase) = do
  exists <- doesFileExist src
  when (not exists) $
    throwCsExceptionIO (CmdLineError ("does not exist: " ++ src))

  let dflags = cs_dflags cs_env
      mb_o_file = outputFile dflags
      cs_link = csLink dflags

      output
        | NoStop <- stop_phase, not (isNoLink cs_link) = Persistent
        | isJust mb_o_file = SpecificFile
        | otherwise = Persistent

      pipe_env = mkPipeEnv stop_phase src mb_phase output
      pipeline = pipelineStart pipe_env (setDumpPrefix pipe_env cs_env) src mb_phase
  runPipeline pipeline

doLink :: CsEnv -> [FilePath] -> IO ()
doLink cs_env o_files = do
  let dflags = cs_dflags cs_env
      logger = cs_logger cs_env
      unit_env = cs_unit_env cs_env
      tmpfs = cs_tmpfs cs_env
      fc = cs_FC cs_env
  case csLink dflags of
    NoLink -> return ()
    LinkBinary -> linkBinary logger tmpfs dflags unit_env o_files []
    LinkStaticLib -> linkStaticLib logger dflags unit_env o_files []
    LinkDynLib -> linkDynLibCheck logger tmpfs dflags unit_env o_files []
    LinkMergedObj
      | Just out <- outputFile dflags
      , let objs = [ f | FileOption _ f <- ldInputs dflags ]
        -> joinObjectFiles cs_env (o_files ++ objs) out
      | otherwise -> panic "Output path must be specified for LinkMergedObj"

-- -----------------------------------------------------------------------------
-- Environment Initialisation

mkPipeEnv :: StopPhase -> FilePath -> Maybe Phase -> PipelineOutput -> PipeEnv
mkPipeEnv stop_phase input_fn start_phase output =
  let (basename, suffix) = splitExtension input_fn
      suffix' = drop 1 suffix
  in PipeEnv
     { stop_phase = stop_phase
     , src_filename = input_fn
     , src_basename = basename
     , src_suffix = suffix
     , start_phase = fromMaybe (startPhase suffix') start_phase
     , output_spec = output
     }

setDumpPrefix :: PipeEnv -> CsEnv -> CsEnv
setDumpPrefix pipe_env cs_env =
  csUpdateFlags (\dflags -> dflags { dumpPrefix = src_basename pipe_env ++ "." }) cs_env

-- -----------------------------------------------------------------------------
-- The Pipelines

preprocessPipeline :: P m => PipeEnv -> CsEnv -> FilePath -> m DynFlags
preprocessPipeline pipe_env cs_env input_fn = do
  (dflags, p_warns, warns) <- use (T_FileArgs cs_env input_fn)

  let print_config = initPrintConfig dflags
      logger = cs_logger cs_env
      diag_opts = initDiagOpts dflags
  liftIO $ printOrThrowDiagnostics logger print_config diag_opts (CsPsMessage <$> p_warns)
  liftIO $ printOrThrowDiagnostics logger print_config diag_opts (CsDriverMessage <$> warns)
  return dflags

fullPipeline :: P m => PipeEnv -> CsEnv -> FilePath -> CsSource -> m (ModIface, HomeModLinkable)
fullPipeline pipe_env cs_env0 input_fn src_flavor = do
  dflags <- preprocessPipeline pipe_env cs_env0 input_fn
  let cs_env1 = csSetFlags dflags cs_env0
  (cs_env2, mod_sum, cs_recomp_status) <-
    use (T_CsRecomp pipe_env cs_env1 input_fn src_flavor)
  csPipeline pipe_env (cs_env2, mod_sum, cs_recomp_status)

csPipeline
  :: P m => PipeEnv -> (CsEnv, ModSummary, CsRecompStatus) -> m (ModIface, HomeModLinkable)
csPipeline pipe_env (cs_env, mod_sum, cs_recomp_status) = do
  case cs_recomp_status of
    CsUpToDate iface mb_linkable -> return (iface, mb_linkable)
    CsRecompNeeded mb_old_hash -> do
      (tc_result, warnings) <- use (T_Cs cs_env mod_sum)
      csBackendAction <- use (T_CsPostTc cs_env mod_sum tc_result warnings mb_old_hash)
      csBackendPipeline pipe_env cs_env mod_sum csBackendAction

csBackendPipeline
  :: P m => PipeEnv -> CsEnv -> ModSummary -> CsBackendAction -> m (ModIface, HomeModLinkable)
csBackendPipeline pipe_env cs_env mod_sum result =
  if backendGeneratesCode (backend (cs_dflags cs_env))
  then do res <- csGenBackendPipeline pipe_env cs_env mod_sum result
          when (gopt Opt_BuildDynamicToo (cs_dflags cs_env)
                && backendWritesFiles (backend (cs_dflags cs_env))) $ 
            let dflags' = setDynamicNow (cs_dflags cs_env)
            in () <$ csGenBackendPipeline pipe_env (csSetFlags dflags' cs_env) mod_sum result
          return res
  else case result of
         CsRecomp {} -> (,) <$> liftIO
                                (mkFullIface cs_env (cs_partial_iface result) Nothing Nothing)
                            <*> pure emptyHomeModInfoLinkable

csGenBackendPipeline
  :: P m => PipeEnv -> CsEnv -> ModSummary -> CsBackendAction -> m (ModIface, HomeModLinkable)
csGenBackendPipeline pipe_env cs_env mod_sum result = do
  let mod_name = moduleName (ms_mod mod_sum)
      src_flavor = ms_cs_src mod_sum
      location = ms_location mod_sum
  (fos, miface, mlinkable, o_file) <-
    use (T_CsBackend pipe_env cs_env mod_name src_flavor location result)
  final_fp <- csPostBackendPipeline
    pipe_env cs_env (ms_cs_src mod_sum) (backend (cs_dflags cs_env)) (Just location) o_file
  final_linkable <-
    case final_fp of
      Nothing -> return mlinkable
      Just o_fp -> do
        unlinked_time <- liftIO (liftIO getCurrentTime)
        final_unlinked <- DotO <$> use (T_MergeForeign pipe_env cs_env o_fp fos)
        let !linkable = LM unlinked_time (ms_mod mod_sum) [final_unlinked]
        return (mlinkable { homeMod_object = Just linkable })
  return (miface, final_linkable)

llvmPipeline :: P m => PipeEnv -> CsEnv -> Maybe ModLocation -> FilePath -> m (Maybe FilePath)
llvmPipeline pipe_env cs_env location fp = do
  opt_fn <- use (T_LlvmOpt pipe_env cs_env fp)
  llvmLlcPipeline pipe_env cs_env location opt_fn

llvmLlcPipeline :: P m => PipeEnv -> CsEnv -> Maybe ModLocation -> FilePath -> m (Maybe FilePath)
llvmLlcPipeline pipe_env cs_env location opt_fn = do
  llc_fn <- use (T_LlvmLlc pipe_env cs_env opt_fn)
  lasPipeline pipe_env cs_env location llc_fn

lasPipeline :: P m => PipeEnv -> CsEnv -> Maybe ModLocation -> FilePath -> m (Maybe ObjFile)
lasPipeline pipe_env cs_env location input_fn =
  case stop_phase pipe_env of
    StopAs -> return Nothing
    _ -> Just <$> use (T_LlvmAs pipe_env cs_env location input_fn)

csPostBackendPipeline
  :: P m
  => PipeEnv
  -> CsEnv
  -> CsSource
  -> Backend
  -> Maybe ModLocation
  -> FilePath
  -> m (Maybe FilePath)
csPostBackendPipeline pipe_env cs_env CsSrcFile bcknd ml input_fn =
  applyPostCsPipeline (backendPostCsPipeline bcknd) pipe_env cs_env ml input_fn

applyPostCsPipeline
  :: P m
  => DefunctionalizedPostCsPipeline
  -> PipeEnv
  -> CsEnv
  -> Maybe ModLocation
  -> FilePath
  -> m (Maybe FilePath)
applyPostCsPipeline LlvmPostCsPipeline = llvmPipeline
applyPostCsPipeline NoPostCsPipeline = \_ _ _ _ -> return Nothing  

pipelineStart :: P m => PipeEnv -> CsEnv -> FilePath -> Maybe Phase -> m (Maybe FilePath)
pipelineStart pipe_env cs_env input_fn mb_phase =
  fromPhase (fromMaybe (startPhase $ src_suffix pipe_env) mb_phase)
  where
    stop_after = stop_phase pipe_env
    frontend :: P m => CsSource -> m (Maybe FilePath)
    frontend sf = case stop_after of
                    NoStop -> objFromLinkable <$> fullPipeline pipe_env cs_env input_fn sf

    objFromLinkable (_, homeMod_object -> Just (LM _ _ [DotO lnk])) = Just lnk
    objFromLinkable _ = Nothing

    fromPhase :: P m => Phase -> m (Maybe FilePath)
    fromPhase (Cs p) = frontend p
    fromPhase LlvmOpt = llvmPipeline pipe_env cs_env Nothing input_fn
    fromPhase LlvmLlc = llvmLlcPipeline pipe_env cs_env Nothing input_fn
    fromPhase StopLn = return (Just input_fn)
    fromPhase MergeForeign = panic "fromPhase: MergeForeign"
