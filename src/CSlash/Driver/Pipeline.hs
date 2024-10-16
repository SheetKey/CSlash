{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
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
import CSlash.Iface.Recomp
import CSlash.Types.Unique.DSet

type P m = TPipelineClass TPhase m

-- ---------------------------------------------------------------------------
-- Pre-process

preprocess
  :: CsEnv
  -> FilePath
  -> Maybe InputFileBuffer
  -> Maybe Phase
  -> IO (Either DriverMessages (DynFlags, FilePath))
preprocess cs_env input_fn mb_input_buf mb_phase =
  handleSourceError (\err -> return $ Left $ to_driver_messages $ srcErrorMessages err)
  $ MC.handle handler
  $ fmap Right $ do
  massertPpr (isJust mb_phase || isCsSrcFilename input_fn) (text input_fn)
  input_fn_final <- mkInputFn
  let preprocess_pipeline
        = preprocessPipeline pipe_env (setDumpPrefix pipe_env cs_env) input_fn_final
  (, input_fn_final) <$> runPipeline preprocess_pipeline

  where
    srcspan = srcLocSpan $ mkSrcLoc (mkFastString input_fn) 1 1
    handler (ProgramError msg) = return $ Left $ singleMessage $
                                 mkPlainErrorMsgEnvelope srcspan $
                                 DriverUnknownMessage $ mkSimpleUnknownDiagnostic $
                                 mkPlainError noHints $ text msg
    handler ex = throwCsExceptionIO ex

    to_driver_messages :: Messages CsMessage -> Messages DriverMessage
    to_driver_messages msgs = case traverse to_driver_message msgs of
      Nothing -> pprPanic "non-driver message in preproess"
                 (vcat $ pprMsgEnvelopeBagWithLoc
                   (defaultDiagnosticOpts @CsMessage) (getMessages msgs))
      Just msgs' -> msgs'

    to_driver_message = \case
      CsDriverMessage msg -> Just msg
      CsPsMessage (PsHeaderMessage msg) -> Just (DriverPsHeaderMessage (PsHeaderMessage msg))
      _ -> Nothing

    pipe_env = mkPipeEnv StopPreprocess input_fn mb_phase (Temporary TFL_CslSession)
    mkInputFn = case mb_input_buf of
                  Just input_buf -> panic "mkInputFn: Just buf passed to preprocess"
                  Nothing -> return input_fn

-- ---------------------------------------------------------------------------
-- Compile

compileOne
  :: CsEnv
  -> ModSummary
  -> Int
  -> Int
  -> Maybe ModIface
  -> HomeModLinkable
  -> IO HomeModInfo
compileOne = compileOne' (Just batchMsg)

compileOne'
  :: Maybe Messager
  -> CsEnv
  -> ModSummary
  -> Int
  -> Int
  -> Maybe ModIface
  -> HomeModLinkable
  -> IO HomeModInfo
compileOne' mCsMessage cs_env0 summary mod_index nmods mb_old_iface mb_old_linkable = do
  debugTraceMsg logger 2 (text "compile: input file" <+> text input_fn)

  massertPpr (input_fn == input_fn') $ text input_fn <+> text "/=" <+> text input_fn'

  unless (gopt Opt_KeepHiFiles lcl_dflags) $
    addFilesToClean tmpfs TFL_CurrentModule [ml_hi_file $ ms_location summary]

  unless (gopt Opt_KeepOFiles lcl_dflags) $
    addFilesToClean tmpfs TFL_CslSession [ml_obj_file $ ms_location summary]

  let pipe_env = mkPipeEnv NoStop input_fn Nothing pipelineOutput
  status <- csRecompStatus
              mCsMessage
              cs_env
              upd_summary
              mb_old_iface
              mb_old_linkable
              (mod_index, nmods)
  let pipeline = csPipeline pipe_env (setDumpPrefix pipe_env cs_env, upd_summary, status)
  (iface, linkable) <- runPipeline pipeline
  details <- initModDetails cs_env iface
  return $! HomeModInfo iface details linkable
  where
    lcl_dflags = ms_cs_opts summary
    location = ms_location summary
    input_fn = expectJust "compile:cs" (ml_cs_file location)
    input_fn' = ms_cs_file summary

    pipelineOutput = backendPipelineOutput bcknd

    logger = cs_logger cs_env0
    tmpfs = cs_tmpfs cs_env0

    basename = dropExtension input_fn

    current_dir = takeDirectory basename
    old_paths = includePaths lcl_dflags
    (bcknd, dflags3) = (backend dflags, lcl_dflags)

    dflags = dflags3 { includePaths = offsetIncludePaths dflags3
                                      $ addImplicitQuoteInclude old_paths [current_dir] }
    upd_summary = summary { ms_cs_opts = dflags }
    cs_env = csSetFlags dflags cs_env0

    offsetIncludePaths :: DynFlags -> IncludeSpecs -> IncludeSpecs
    offsetIncludePaths dflags (IncludeSpecs incs quotes impl) =
      let go = map (augmentByWorkingDirectory dflags)
      in IncludeSpecs (go incs) (go quotes) (go impl)

-- ---------------------------------------------------------------------------
-- Link

link
  :: CsLink
  -> Logger
  -> TmpFs
  -> FinderCache
  -> DynFlags
  -> UnitEnv
  -> Bool
  -> Maybe (RecompileRequired -> IO ())
  -> HomePackageTable
  -> IO SuccessFlag
link csLink logger tmpfs fc dflags unit_env batch_attempt_linking mCsMessage hpt =
  case csLink of
    NoLink -> return Succeeded
    LinkBinary -> normal_link
    LinkStaticLib -> normal_link
    LinkDynLib -> normal_link
    LinkMergedObj -> normal_link
  where
    normal_link = link' logger tmpfs fc dflags unit_env batch_attempt_linking mCsMessage hpt

link'
  :: Logger
  -> TmpFs
  -> FinderCache
  -> DynFlags
  -> UnitEnv
  -> Bool
  -> Maybe (RecompileRequired -> IO ())
  -> HomePackageTable
  -> IO SuccessFlag
link' logger tmpfs fc dflags unit_env batch_attempt_linking mCsMessager hpt
  | batch_attempt_linking
  = do panic "link'"
  | otherwise
  = panic "link'"

-- -----------------------------------------------------------------------------
-- Compile files in one-shot mode.

oneShot :: CsEnv -> StopPhase -> [(String, Maybe Phase) ] -> IO ()
oneShot cs_env stop_phase srcs = do
  o_files <- mapMaybeM (compileFile cs_env stop_phase) srcs
  case stop_phase of
    StopPreprocess -> return ()
    StopAs -> return ()
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
                    StopPreprocess -> do
                      _ <- preprocessPipeline pipe_env cs_env input_fn
                      let logger = cs_logger cs_env
                      final_fn <- liftIO
                        $ phaseOutputFilenameNew (Cs CsSrcFile) pipe_env cs_env Nothing
                      when (final_fn /= input_fn) $ do
                        panic "pipelineStart bad file names"
                      return Nothing
                    _ -> objFromLinkable <$> fullPipeline pipe_env cs_env input_fn sf

    objFromLinkable (_, homeMod_object -> Just (LM _ _ [DotO lnk])) = Just lnk
    objFromLinkable _ = Nothing

    fromPhase :: P m => Phase -> m (Maybe FilePath)
    fromPhase (Cs p) = frontend p
    fromPhase As = panic "fromPhase As"
    fromPhase LlvmOpt = llvmPipeline pipe_env cs_env Nothing input_fn
    fromPhase LlvmLlc = llvmLlcPipeline pipe_env cs_env Nothing input_fn
    fromPhase StopLn = return (Just input_fn)
    fromPhase MergeForeign = panic "fromPhase: MergeForeign"
