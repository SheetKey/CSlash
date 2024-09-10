module CSlash.Settings where

import CSlash.Utils.Fingerprint

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
