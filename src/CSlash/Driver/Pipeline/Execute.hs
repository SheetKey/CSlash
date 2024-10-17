{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DerivingVia #-}

module CSlash.Driver.Pipeline.Execute where

-- import GHC.Iface.Make
-- import {-# SOURCE #-} GHC.Driver.Pipeline (compileForeign, compileEmptyStub)
-- import GHC.Runtime.Loader (initializePlugins)
import CSlash.Rename.Names
import CSlash.Linker.ExtraObj
import CSlash.Linker.Dynamic

import CSlash.Data.Maybe
import CSlash.Data.StringBuffer
import CSlash.Driver.Backend
import CSlash.Driver.Config.Finder
import CSlash.Driver.Config.Parser
import CSlash.Driver.Env
import CSlash.Driver.Env.KnotVars
import CSlash.Driver.Errors.Types
import CSlash.Driver.LlvmConfigCache (readLlvmConfigCache)
import CSlash.Driver.Main
import CSlash.Driver.Phases
import CSlash.Driver.Pipeline.Monad
import CSlash.Driver.Pipeline.Phases
import CSlash.Driver.Session
import CSlash.Parser.Header
import CSlash.Platform
import CSlash.Platform.Ways
import CSlash.Settings
import CSlash.SysTools
import CSlash.Tc.Types
import CSlash.Types.Error
import CSlash.Types.Name.Env
import CSlash.Types.SourceError
import CSlash.Types.SourceFile
import CSlash.Types.SrcLoc
import CSlash.Unit.Env
import CSlash.Unit.Finder
import CSlash.Unit.Home
import CSlash.Unit.Info
import CSlash.Unit.Module.Env
import CSlash.Unit.Module.Location
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.ModSummary
import CSlash.Unit.Module.Status
import CSlash.Unit.State
import CSlash.Unit.Types
import CSlash.Utils.Error
import CSlash.Utils.Fingerprint
import CSlash.Utils.Logger
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.TmpFs
-- import CSlash.Utils.Touch
import Control.Monad
import Control.Monad.Catch
import Control.Monad.IO.Class
import Control.Monad.Trans.Reader
import Data.IORef
import Data.List (intercalate, isInfixOf)
import Data.Maybe
import System.Directory
import System.FilePath
import System.IO

import CSlash.Llvm.Config (LlvmTarget(..), LlvmConfig(..))

import CSlash.Language.Syntax.Module.Name
import CSlash.Unit.Home.ModInfo

newtype Use a = Use { runUse :: PhaseHook -> IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadThrow, MonadCatch)
  via (ReaderT PhaseHook IO)

instance MonadUse TPhase Use where
  use fa = Use $ \(PhaseHook k) -> k fa

runPipeline :: Use a -> IO a
runPipeline pipeline = runUse pipeline (PhaseHook runPhase)

runPhase :: TPhase out -> IO out
runPhase (T_FileArgs cs_env inp_path) = getFileArgs cs_env inp_path
runPhase (T_CsRecomp pipe_env cs_env fp cs_src) = runCsPhase pipe_env cs_env fp cs_src
runPhase (T_Cs cs_env mod_sum) = runCsTcPhase cs_env mod_sum
runPhase (T_CsPostTc cs_env ms fer m mfi) = runCsPostTcPhase cs_env ms fer m mfi
runPhase (T_CsBackend pipe_env cs_env mod_name cs_src location x)
  = runCsBackendPhase pipe_env cs_env mod_name cs_src location x
runPhase (T_LlvmOpt pipe_env cs_env input_fn) = runLlvmOptPhase pipe_env cs_env input_fn
runPhase (T_LlvmLlc pipe_env cs_env input_fn) = runLlvmLlcPhase pipe_env cs_env input_fn
runPhase (T_LlvmAs pipe_env cs_env location input_fn)
  = runLlvmAsPhase pipe_env cs_env location input_fn
runPhase (T_MergeForeign pipe_env cs_env input_fn fs) = runMergeForeign pipe_env cs_env input_fn fs

runMergeForeign :: PipeEnv -> CsEnv -> FilePath -> [FilePath] -> IO FilePath
runMergeForeign _ cs_env input_fn foreign_os = 
  if null foreign_os
  then return input_fn
  else do
    new_o <- newTempName (cs_logger cs_env) (cs_tmpfs cs_env)
                         (tmpDir (cs_dflags cs_env))
                         TFL_CurrentModule "o"
    copyFile input_fn new_o
    joinObjectFiles cs_env (new_o : foreign_os) input_fn
    return input_fn

runLlvmLlcPhase :: PipeEnv -> CsEnv -> FilePath -> IO FilePath
runLlvmLlcPhase pipe_env cs_env input_fn = do
  llvm_config <- readLlvmConfigCache (cs_llvm_config cs_env)
  let dflags = cs_dflags cs_env
      logger = cs_logger cs_env
      llvmOpts = case llvmOptLevel dflags of
        0 -> "-O0"
        1 -> "-O1"
        2 -> "-O2"
        _ -> "-O3"

      defaultOptions = map Option . concatMap words . snd
                       $ unzip (llvmOptions llvm_config dflags)
      optFlag = if null (getOpts dflags opt_lc)
                then map Option $ words llvmOpts
                else []

      next_phase = As

  output_fn <- phaseOutputFilenameNew next_phase pipe_env cs_env Nothing

  runLlvmLlc logger dflags
    (optFlag
     ++ defaultOptions
     ++ [ FileOption "" input_fn
        , Option "-o"
        , FileOption "" output_fn
        ]
    )

  return output_fn

runLlvmOptPhase :: PipeEnv -> CsEnv -> FilePath -> IO FilePath
runLlvmOptPhase pipe_env cs_env input_fn = do
  let dflags = cs_dflags cs_env
      logger = cs_logger cs_env
  llvm_config <- readLlvmConfigCache (cs_llvm_config cs_env)
  let optIdx = max 0 $ min 3 $ llvmOptLevel dflags
      llvmOpts = case lookup optIdx $ llvmPasses llvm_config of
                   Just passes -> passes
                   Nothing -> panic ("runPhase LlvmOpt: llvm-passes file "
                                     ++ "is missing passes for level "
                                     ++ show optIdx)
      defaultOptions = map Option . concat . fmap words . fst
                       $ unzip (llvmOptions llvm_config dflags)

      optFlag = if null (getOpts dflags opt_lo)
                then map Option $ words llvmOpts
                else []

  output_fn <- phaseOutputFilenameNew LlvmLlc pipe_env cs_env Nothing

  runLlvmOpt logger dflags
    (optFlag
     ++ defaultOptions
     ++ [ FileOption "" input_fn
        , Option "-o"
        , FileOption "" output_fn
        ]
    )

  return output_fn

runGenericAsPhase
  :: (Logger -> DynFlags -> [Option] -> IO ())
  -> [Option]
  -> PipeEnv
  -> CsEnv
  -> Maybe ModLocation
  -> FilePath
  -> IO FilePath
runGenericAsPhase run_as extra_opts pipe_env cs_env location input_fn = do
  let dflags = cs_dflags cs_env
      logger = cs_logger cs_env

      cmdline_include_paths = includePaths dflags
      pic_c_flags = picCCOpts dflags

  output_fn <- phaseOutputFilenameNew StopLn pipe_env cs_env location

  createDirectoryIfMissing True (takeDirectory output_fn)

  let global_includes = [ Option ("-I" ++ p)
                        | p <- includePathsGlobal cmdline_include_paths ]
      local_includes = [ Option ("-iquote" ++ p)
                       | p <- includePathsQuote cmdline_include_paths ]
      runAssembler inputFilename outputFilename
        = withAtomicRename outputFilename $ \temp_outputFilename ->
            run_as
              logger
              dflags
              (local_includes ++ global_includes
               ++ map Option pic_c_flags
               ++ [ Option "-x"
                  , Option "assembler"
                  , Option "-c"
                  , FileOption "" inputFilename
                  , Option "-o"
                  , FileOption "" temp_outputFilename
                  ]
                ++ extra_opts
              )

  debugTraceMsg logger 4 (text "Running the assembler")
  runAssembler input_fn output_fn

  return output_fn

runLlvmAsPhase :: PipeEnv -> CsEnv -> Maybe ModLocation -> FilePath -> IO FilePath
runLlvmAsPhase =
  runGenericAsPhase runLlvmAs [ Option "-Wno-unused-command-line-argument" ]

runCsBackendPhase
  :: PipeEnv
  -> CsEnv
  -> ModuleName
  -> CsSource
  -> ModLocation
  -> CsBackendAction
  -> IO ([FilePath], ModIface, HomeModLinkable, FilePath)
runCsBackendPhase pipe_env cs_env mod_name src_flavor location result =
  let dflags = cs_dflags cs_env
      logger = cs_logger cs_env
      o_file = if dynamicNow dflags then ml_dyn_obj_file location else ml_obj_file location
      next_phase = csPostBackendPhase src_flavor (backend dflags)
  in case result of
       CsRecomp { cs_guts = cgguts, cs_mod_location = mod_location
                , cs_partial_iface = partial_iface, cs_old_iface_hash = mb_old_iface_hash }
         | not (backendGeneratesCode (backend dflags))
           -> panic "CsRecomp not relevant for NoBackend"
         | backendWritesFiles (backend dflags)
           -> do
             output_fn <- phaseOutputFilenameNew next_phase pipe_env cs_env (Just location)
             panic "csGenHardCode not implemented"
         | otherwise
           -> panic "unreachable"
              
getFileArgs :: CsEnv -> FilePath -> IO ((DynFlags, Messages PsMessage, Messages DriverMessage))
getFileArgs cs_env input_fn = do
  let dflags0 = cs_dflags cs_env
      parser_opts = initParserOpts dflags0
  (warns0, src_opts) <- getOptionsFromFile parser_opts input_fn
  (dflags1, unhandled_flags, warns)
    <- parseDynamicFilePragma dflags0 src_opts
  checkProcessArgsResult unhandled_flags
  return (dflags1, warns0, warns)

runCsPhase
  :: PipeEnv
  -> CsEnv
  -> FilePath
  -> CsSource
  -> IO (CsEnv, ModSummary, CsRecompStatus)
runCsPhase pipe_env cs_env0 input_fn src_flavor = do
  let dflags0 = cs_dflags cs_env0
      PipeEnv { src_basename = basename, src_suffix = suff } = pipe_env

      current_dir = takeDirectory basename
      paths = includePaths dflags0
      new_includes = addImplicitQuoteInclude paths [current_dir]
      dflags = dflags0 { includePaths = new_includes }
      cs_env = csSetFlags dflags cs_env0

  (cs_buf, mod_name, imps, csl_prim_imp) <- do
    buf <- hGetStringBuffer input_fn
    let imp_prelude = True
        popts = initParserOpts dflags
        rn_pkg_qual = renameRawPkgQual (cs_unit_env cs_env)
        rn_imps = fmap (\(rpk, lmn@(L _ mn)) -> (rn_pkg_qual mn rpk, lmn))
    eimps <- getImports popts imp_prelude buf input_fn (basename <.> suff)
    case eimps of
      Left errs -> throwErrors (CsPsMessage <$> errs)
      Right (imps, csl_prim_imp, L _ mod_name) -> return
        (Just buf, mod_name, rn_imps imps, csl_prim_imp)

  location <- mkOneShotModLocation pipe_env dflags src_flavor mod_name
  let o_file = ml_obj_file location
      hi_file = ml_hi_file location
      hie_file = ml_hie_file location
      dyn_o_file = ml_dyn_obj_file location

  src_hash <- getFileHash (basename <.> suff)
  hi_date <- modificationTimeIfExists hi_file
  hie_date <- modificationTimeIfExists hie_file
  o_mod <- modificationTimeIfExists o_file
  dyn_o_mod <- modificationTimeIfExists dyn_o_file

  mod <- let home_unit = cs_home_unit cs_env
             fc = cs_FC cs_env
         in addHomeModuleToFinder fc home_unit mod_name location

  let mod_summary = ModSummary
        { ms_mod = mod
        , ms_cs_src = src_flavor
        , ms_cs_file = input_fn
        , ms_cs_opts = dflags
        , ms_cs_buf = cs_buf
        , ms_location = location
        , ms_cs_hash = src_hash
        , ms_obj_date = o_mod
        , ms_dyn_obj_date = dyn_o_mod
        , ms_parsed_mod = Nothing
        , ms_iface_date = hi_date
        , ms_hie_date = hie_date
        , ms_csl_prim_import = csl_prim_imp
        , ms_textual_imps = imps
        }

      msg :: Messager
      msg cs_env _ what _ = oneShotMsg (cs_logger cs_env) what

  type_env_var <- newIORef emptyNameEnv
  let cs_env' = cs_env
        { cs_type_env_vars = knotVarsFromModuleEnv (mkModuleEnv [(mod, type_env_var)]) }

  status <- csRecompStatus (Just msg) cs_env' mod_summary Nothing emptyHomeModInfoLinkable (1, 1)

  return (cs_env', mod_summary, status)

mkOneShotModLocation :: PipeEnv -> DynFlags -> CsSource -> ModuleName -> IO ModLocation
mkOneShotModLocation pipe_env dflags src_flavor mod_name = do
  let PipeEnv { src_basename = basename, src_suffix = suff } = pipe_env
      location1 = mkHomeModLocation2 fopts mod_name basename suff
      location2 = location1

      ohi = outputHi dflags
      location3 | Just fn <- ohi = location2 { ml_hi_file = fn }
                | otherwise = location2

      dynohi = dynOutputHi dflags
      location4 | Just fn <- dynohi = location3 { ml_dyn_hi_file = fn }
                | otherwise = location3

      expl_o_file = outputFile_ dflags
      expl_dyn_o_file = dynOutputFile_ dflags
      location5 | Just ofile <- expl_o_file
                , let dyn_ofile = fromMaybe (ofile -<.> dynObjectSuf_ dflags) expl_dyn_o_file
                , isNoLink (csLink dflags)
                = location4 { ml_obj_file = ofile
                            , ml_dyn_obj_file = dyn_ofile
                            }
                | Just dyn_ofile <- expl_dyn_o_file
                = location4 { ml_dyn_obj_file = dyn_ofile }
                | otherwise
                = location4

  return location5
  where
    fopts = initFinderOpts dflags

runCsTcPhase :: CsEnv -> ModSummary -> IO (FrontendResult, Messages CsMessage)
runCsTcPhase = csTypecheckAndGetWarnings

runCsPostTcPhase
  :: CsEnv
  -> ModSummary
  -> FrontendResult
  -> Messages CsMessage
  -> Maybe Fingerprint
  -> IO CsBackendAction
runCsPostTcPhase cs_env mod_summary tc_result tc_warnings mb_old_hash =
  runCs cs_env $ csDesugarAndSimplify mod_summary tc_result tc_warnings mb_old_hash
  

phaseOutputFilenameNew :: Phase -> PipeEnv -> CsEnv -> Maybe ModLocation -> IO FilePath
phaseOutputFilenameNew next_phase pipe_env cs_env maybe_loc =
  let PipeEnv { stop_phase = stop_phase, src_basename = src_basename, output_spec = output_spec }
        = pipe_env

      dflags = cs_dflags cs_env
      logger = cs_logger cs_env
      tmpfs = cs_tmpfs cs_env
  in getOutputFilename logger tmpfs (stopPhaseToPhase stop_phase) output_spec
                      src_basename dflags next_phase maybe_loc

getOutputFilename
  :: Logger
  -> TmpFs
  -> Phase
  -> PipelineOutput
  -> String
  -> DynFlags
  -> Phase
  -> Maybe ModLocation
  -> IO FilePath
getOutputFilename logger tmpfs stop_phase output basename dflags next_phase maybe_location
  | StopLn <- next_phase, Just loc <- maybe_location
  = return $ if dynamicNow dflags
             then ml_dyn_obj_file loc
             else ml_obj_file loc
  | is_last_phase, Persistent <- output
  = persistent_fn
  | is_last_phase, SpecificFile <- output
  = return $ if dynamicNow dflags
             then case dynOutputFile_ dflags of
                    Nothing -> let ofile = getOutputFile_ dflags
                                   new_ext = case takeExtension ofile of
                                               "" -> "dyn"
                                               ext -> "dyn_" ++ tail ext
                               in replaceExtension ofile new_ext
                    Just fn -> fn
             else getOutputFile_ dflags
  | keep_this_output
  = persistent_fn
  | Temporary lifetime <- output
  = newTempName logger tmpfs (tmpDir dflags) lifetime suffix
  | otherwise 
  = newTempName logger tmpfs (tmpDir dflags) TFL_CurrentModule suffix
  where
    getOutputFile_ dflags = case outputFile_ dflags of
      Nothing -> pprPanic "SpecificFile: No filename"
                           (ppr (dynamicNow dflags) $$
                            text (fromMaybe "-" (dynOutputFile_ dflags)))
      Just fn -> fn

    odir = objectDir dflags
    osuf = objectSuf dflags
    keep_s = gopt Opt_KeepSFiles dflags
    keep_bc = gopt Opt_KeepLlvmFiles dflags

    myPhaseInputExt MergeForeign = osuf
    myPhaseInputExt StopLn = osuf
    myPhaseInputExt other = phaseInputExt other

    is_last_phase = next_phase `eqPhase` stop_phase

    keep_this_output = case next_phase of
                         As      | keep_s -> True
                         LlvmOpt | keep_bc -> True
                         _ -> False

    suffix = myPhaseInputExt next_phase

    persistent_fn
      | StopLn <- next_phase = return odir_persistent
      | otherwise = return persistent

    persistent = basename <.> suffix

    odir_persistent
      | Just d <- odir = (d </> persistent)
      | otherwise = persistent

llvmOptions :: LlvmConfig -> DynFlags -> [(String, String)]
llvmOptions llvm_config dflags =
     [ ( "-relocation-model=" ++ rmodel
       , "-relocation-model=" ++ rmodel )
     | not (null rmodel) ]
  ++ [ ("", "-mcpu=" ++ mcpu)
     | not (null mcpu)
     , not (any (isInfixOf "-mcpu") (getOpts dflags opt_lc)) ]
  ++ [ ("", "-mattr=" ++ attrs) | not (null attrs) ]
  ++ [ ("", "-target-abi=" ++ abi) | not (null abi) ]
  where
    target = platformMisc_llvmTarget $ platformMisc dflags
    Just (LlvmTarget _ mcpu mattr) = lookup target (llvmTargets llvm_config)

    rmodel | gopt Opt_PIC dflags = "pic"
           | positionIndependent dflags = "pic"
           | ways dflags `hasWay` WayDyn = "dynamic-no-pic"
           | otherwise = "static"

    platform = targetPlatform dflags
    arch = platformArch platform

    attrs :: String
    attrs = intercalate "," $ mattr
            -- ++ [ "+sse42"  | isSse4_2Enabled dflags ]
            -- ++ ["+sse2"    | isSse2Enabled platform   ]
            -- ++ ["+sse"     | isSseEnabled platform    ]
            -- ++ ["+avx512f" | isAvx512fEnabled dflags  ]
            -- ++ ["+avx2"    | isAvx2Enabled dflags     ]
            -- ++ ["+avx"     | isAvxEnabled dflags      ]
            -- ++ ["+avx512cd"| isAvx512cdEnabled dflags ]
            -- ++ ["+avx512er"| isAvx512erEnabled dflags ]
            -- ++ ["+avx512pf"| isAvx512pfEnabled dflags ]
            -- ++ ["+fma"     | isFmaEnabled dflags && (arch /= ArchAArch64) ]
            -- ++ ["+bmi"     | isBmiEnabled dflags      ]
            -- ++ ["+bmi2"    | isBmi2Enabled dflags     ]

    abi :: String
    abi = case arch of
            _ -> ""

csPostBackendPhase :: CsSource -> Backend -> Phase
csPostBackendPhase CsSrcFile bcknd = backendNormalSuccessorPhase bcknd

-- ---------------------------------------------------------------------------
-- join object files into a single relocatable object file, using ld -r

joinObjectFiles :: CsEnv -> [FilePath] -> FilePath -> IO ()
joinObjectFiles cs_env o_files output_fn
  | can_merge_objs = 
    let toolSettings' = toolSettings dflags
        ldIsGnuLd = toolSettings_ldIsGnuLd toolSettings'
        ld_r args = runMergeObjects
                      (cs_logger cs_env) (cs_tmpfs cs_env) (cs_dflags cs_env)
                      ([ Option "-o"
                       , FileOption "" output_fn ]
                       ++ args)
    in if ldIsGnuLd
       then do script <- newTempName logger tmpfs (tmpDir dflags) TFL_CurrentModule "ldscript"
               cwd <- getCurrentDirectory
               let o_files_abs = map (\x -> "\"" ++ (cwd </> x) ++ "\"") o_files
               writeFile script $ "INPUT(" ++ unwords o_files_abs ++ ")"
               ld_r [FileOption "" script]
       else if toolSettings_ldSupportsFilelist toolSettings'
            then do filelist <- newTempName
                                logger tmpfs (tmpDir dflags) TFL_CurrentModule "filelist"
                    writeFile filelist $ unlines o_files
                    ld_r [ Option "-filelist"
                         , FileOption "" filelist ]
            else ld_r (map (FileOption "") o_files)
  | otherwise =
    withAtomicRename output_fn $ \tmp_ar ->
      liftIO $ runAr logger dflags Nothing $ map Option $ ["qc" ++ dashL, tmp_ar] ++ o_files
  where
    dashLSupported = sArSupportsDashL (settings dflags)
    dashL = if dashLSupported then "L" else ""
    can_merge_objs = isJust (pgm_lm (cs_dflags cs_env))
    dflags = cs_dflags cs_env
    tmpfs = cs_tmpfs cs_env
    logger = cs_logger cs_env

-----------------------------------------------------------------------------

linkDynLibCheck :: Logger -> TmpFs -> DynFlags -> UnitEnv -> [String] -> [UnitId] -> IO ()
linkDynLibCheck logger tmpfs dflags unit_env o_files dep_units = do
  when (haveRtsOptsFlags dflags) $
    logMsg logger MCInfo noSrcSpan
    $ withPprStyle defaultUserStyle
    $ text "Warning: -rtsopts and -with-rtsopts have no effect with -shared."
  linkDynLib logger tmpfs dflags unit_env o_files dep_units
