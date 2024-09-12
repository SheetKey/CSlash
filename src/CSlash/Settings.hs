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

data FileSettings = FileSettings
  { fileSettings_cslUsagePath :: FilePath
  , fileSettings_toolDir :: Maybe FilePath
  , fileSettings_topDir :: FilePath
  , fileSettings_globalPackageDatabase :: FilePath
  }

data CsNameVersion = CsNameVersion
  { csNameVersion_programName :: String
  , csNameVersion_projectVersion :: String
  }

data ToolSettings = ToolSettings
