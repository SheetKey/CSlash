module CSlash.UniqueSubdir (uniqueSubdir) where

import Data.List (intercalate)

import CSlash.Platform.ArchOS
import CSlash.Version (cProjectVersion)

uniqueSubdir :: ArchOS -> FilePath
uniqueSubdir (ArchOS arch os) = intercalate "-"
  [ stringEncodeArch arch
  , stringEncodeOS os
  , cProjectVersion
  ]
