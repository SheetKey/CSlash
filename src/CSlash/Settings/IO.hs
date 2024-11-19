{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CSlash.Settings.IO where

import CSlash.Settings.Utils

import CSlash.Settings.Config
import CSlash.Utils.CliOption
import CSlash.Utils.Fingerprint
import CSlash.Platform
import CSlash.Utils.Panic
import CSlash.Settings
import CSlash.SysTools.BaseDir

import Control.Monad.Trans.Except
import Control.Monad.IO.Class
import qualified Data.Map as Map
import System.FilePath
import System.Directory

data SettingsError
  = SettingsError_MissingData String
  | SettingsError_BadData String

initSettings :: forall m. MonadIO m => String -> ExceptT SettingsError m Settings
initSettings top_dir = do
  let installed :: FilePath -> FilePath
      installed file = top_dir </> file
      libexec :: FilePath -> FilePath
      libexec file = top_dir </> ".." </> "bin" </> file

      settingsFile = installed "settings"

      readFileSafe :: FilePath -> ExceptT SettingsError m String
      readFileSafe path = liftIO (doesFileExist path) >>= \case
        True -> liftIO $ readFile path
        False -> throwE $ SettingsError_MissingData $ "Missing file: " ++ path

  settingsStr <- readFileSafe settingsFile
  settingsList <- case maybeReadFuzzy settingsStr of
    Just s -> pure s
    Nothing -> throwE $ SettingsError_BadData $
               "Can't parse " ++ show settingsFile

  let mySettings = Map.fromList settingsList

      getBooleanSetting :: String -> ExceptT SettingsError m Bool
      getBooleanSetting key = either pgmError pure $
        getRawBooleanSetting settingsFile mySettings key

  useInplaceMinGW <- getBooleanSetting "Use inplace MinGW toolchain"

  mtool_dir <- liftIO $ findToolDir useInplaceMinGW top_dir

  let getSetting key = either pgmError pure $
                       getRawFilePathSetting top_dir settingsFile mySettings key

      getToolSetting :: String -> ExceptT SettingsError m String
      getToolSetting key = expandToolDir useInplaceMinGW mtool_dir <$> getSetting key

  targetPlatformString <- getSetting "target platform string"
  cc_prog <- getToolSetting "C compiler command"
  cc_args_str <- getToolSetting "C compiler flags"
  gccSupportsNoPie <- getBooleanSetting "C compiler supports -no-pie"

  platform <- either pgmError pure $ getTargetPlatform settingsFile mySettings

  let unreg_cc_args = if platformUnregisterised platform
                      then ["-DNO_REGS", "-DUSE_MINIINTERPRETER"]
                      else []
      cc_args = words cc_args_str ++ unreg_cc_args

  ldSupportsFilelist <- getBooleanSetting "ld supports filelist"
  ldSupportsSingleModule <- getBooleanSetting "ld supports single module"
  mergeObjsSupportsResponseFiles <- getBooleanSetting "Merge objects supports response files"
  ldIsGnuLd <- getBooleanSetting "ld is GNU ld"
  arSupportsDashL <- getBooleanSetting "ar supports -L"
  
  let globalpkgdb_path = installed "package.conf.d"
      cs_usage_msg_path = installed "cs-usage.txt"

  unlit_path <- getToolSetting "unlit command"

  windres_path <- getToolSetting "windres command"
  ar_path <- getToolSetting "ar command"
  otool_path <- getToolSetting "otool command"
  install_name_tool_path <- getToolSetting "install_name_tool command"
  ranlib_path <- getToolSetting "ranlib command"

  cc_link_args_str <- getToolSetting "C compiler link flags"
  let ld_prog = cc_prog
      ld_args = map Option (cc_args ++ words cc_link_args_str)
  ld_r_prog <- getToolSetting "Merge objects command"
  ld_r_args <- getToolSetting "Merge objects flags"
  let ld_r
        | null ld_r_prog = Nothing
        | otherwise = Just (ld_r_prog, map Option $ words ld_r_args)

  llvmTarget <- getSetting "LLVM target"

  lc_prog <- getSetting "LLVM llc command"
  lo_prog <- getSetting "LLVM opt command"
  las_prog <- getSetting "LLVM llvm_as command"

  return $ Settings
    { sCsNameVersion = CsNameVersion
      { csNameVersion_programName = "csl"
      , csNameVersion_projectVersion = cProjectVersion
      }

    , sFileSettings = FileSettings
      { fileSettings_csUsagePath = cs_usage_msg_path
      , fileSettings_toolDir = mtool_dir
      , fileSettings_topDir = top_dir
      , fileSettings_globalPackageDatabase = globalpkgdb_path
      }

    , sToolSettings = ToolSettings
      { toolSettings_ldSupportsFilelist = ldSupportsFilelist
      , toolSettings_ldSupportsSingleModule = ldSupportsSingleModule
      , toolSettings_mergeObjsSupportsResponseFiles = mergeObjsSupportsResponseFiles
      , toolSettings_ldIsGnuLd = ldIsGnuLd
      , toolSettings_ccSupportsNoPie = gccSupportsNoPie
      , toolSettings_useInplaceMinGW = useInplaceMinGW
      , toolSettings_arSupportsDashL = arSupportsDashL

      , toolSettings_pgm_L = unlit_path
      , toolSettings_pgm_l = (ld_prog, ld_args)
      , toolSettings_pgm_lm = ld_r
      , toolSettings_pgm_windres = windres_path
      , toolSettings_pgm_ar = ar_path
      , toolSettings_pgm_otool = otool_path
      , toolSettings_pgm_install_name_tool = install_name_tool_path
      , toolSettings_pgm_ranlib = ranlib_path
      , toolSettings_pgm_lo = (lo_prog, [])
      , toolSettings_pgm_lc = (lc_prog, [])
      , toolSettings_pgm_las = (las_prog, [])

      , toolSettings_opt_L = []
      , toolSettings_opt_P = []
      , toolSettings_opt_P_fingerprint = fingerprint0
      , toolSettings_opt_F = []
      , toolSettings_opt_a = []
      , toolSettings_opt_l = []
      , toolSettings_opt_lm = []
      , toolSettings_opt_windres = []
      , toolSettings_opt_lo = []
      , toolSettings_opt_lc = []
      , toolSettings_opt_las = []
      }

    , sTargetPlatform = platform

    , sPlatformMisc = PlatformMisc
      { platformMisc_targetPlatformString = targetPlatformString
      , platformMisc_llvmTarget = llvmTarget
      }

    , sRawSettings = settingsList
    }

getTargetPlatform :: FilePath -> RawSettings -> Either String Platform
getTargetPlatform settingsFile settings = do
  let getBooleanSetting = getRawBooleanSetting settingsFile settings

      readSetting :: (Show a, Read a) => String -> Either String a
      readSetting = readRawSetting settingsFile settings

  targetArchOS <- getTargetArchOS settingsFile settings
  targetWordSize <- readSetting "target word size"
  targetWordBigEndian <- getBooleanSetting "target word big endian"
  targetLeadingUnderscore <- getBooleanSetting "Leading underscore"
  targetUnregisterised <- getBooleanSetting "Unregisterised"
  targetHasGnuNoexecStack <- getBooleanSetting "target has GNU nonexec stack"
  targetHasIdentDirective <- getBooleanSetting "target has .ident directive"
  targetHasSubsectionsViaSymbols <- getBooleanSetting "target has subsections via symbols"
  targetHasLibm <- getBooleanSetting "target has libm"
  crossCompiling <- getBooleanSetting "cross compiling"
  tablesNextToCode <- getBooleanSetting "Tables next to code"

  pure $ Platform
    { platformArchOS = targetArchOS
    , platformWordSize = targetWordSize
    , platformByteOrder = if targetWordBigEndian then BigEndian else LittleEndian
    , platformUnregisterised = targetUnregisterised
    , platformHasGnuNoexecStack = targetHasGnuNoexecStack
    , platformHasIdentDirective = targetHasIdentDirective
    , platformHasSubsectionsViaSymbols = targetHasSubsectionsViaSymbols
    , platformIsCrossCompiling = crossCompiling
    , platformLeadingUnderscore = targetLeadingUnderscore
    , platformTablesNextToCode = tablesNextToCode
    , platformHasLibm = targetHasLibm
    , platform_constants = Nothing
    }
