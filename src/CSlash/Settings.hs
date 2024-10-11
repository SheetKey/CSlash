module CSlash.Settings where

import CSlash.Utils.CliOption
import CSlash.Utils.Fingerprint
import CSlash.Platform

data Settings = Settings
  { sCsNameVersion :: {-# UNPACK #-} !CsNameVersion
  , sFileSettings :: {-# UNPACK #-} !FileSettings
  , sTargetPlatform :: Platform
  , sToolSettings :: {-# UNPACK #-} !ToolSettings
  , sPlatformMisc :: {-# UNPACK #-} !PlatformMisc
  , sRawSettings :: [(String, String)]
  }

data ToolSettings = ToolSettings
  { toolSettings_ldSupportsFilelist :: Bool
  , toolSettings_ldSupportsSingleModule :: Bool
  , toolSettings_mergeObjsSupportsResponseFiles :: Bool
  , toolSettings_ldIsGnuLd :: Bool
  , toolSettings_ccSupportsNoPie :: Bool
  , toolSettings_useInplaceMinGW :: Bool
  , toolSettings_arSupportsDashL :: Bool

  , toolSettings_pgm_L :: String
  , toolSettings_pgm_l :: (String, [Option])
  , toolSettings_pgm_lm :: Maybe (String, [Option])
  , toolSettings_pgm_windres :: String
  , toolSettings_pgm_ar :: String
  , toolSettings_pgm_otool :: String
  , toolSettings_pgm_install_name_tool :: String
  , toolSettings_pgm_ranlib :: String
  , toolSettings_pgm_lo :: (String, [Option])
  , toolSettings_pgm_lc :: (String, [Option])
  , toolSettings_pgm_las :: (String, [Option])

  , toolSettings_opt_L :: [String]
  , toolSettings_opt_P :: [String]
  , toolSettings_opt_P_fingerprint :: Fingerprint
  , toolSettings_opt_F :: [String]
  , toolSettings_opt_a :: [String]
  , toolSettings_opt_l :: [String]
  , toolSettings_opt_lm :: [String]
  , toolSettings_opt_windres :: [String]
  , toolSettings_opt_lo :: [String]
  , toolSettings_opt_lc :: [String]
  , toolSettings_opt_las :: [String]
  }

data FileSettings = FileSettings
  { fileSettings_csUsagePath :: FilePath
  , fileSettings_toolDir :: Maybe FilePath
  , fileSettings_topDir :: FilePath
  , fileSettings_globalPackageDatabase :: FilePath
  }

data CsNameVersion = CsNameVersion
  { csNameVersion_programName :: String
  , csNameVersion_projectVersion :: String
  }

dynLibSuffix :: CsNameVersion -> String
dynLibSuffix (CsNameVersion name ver) = '-' : name ++ ver

-----------------------------------------------------------------------------
-- Accessors from 'Settings'

sArSupportsDashL :: Settings -> Bool
sArSupportsDashL = toolSettings_arSupportsDashL . sToolSettings
