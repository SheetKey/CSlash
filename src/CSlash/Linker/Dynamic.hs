module CSlash.Linker.Dynamic where

import CSlash.Platform
import CSlash.Platform.Ways
import CSlash.Settings (ToolSettings(toolSettings_ldSupportsSingleModule))

-- import GHC.Driver.Config.Linker
import CSlash.Driver.Session

import CSlash.Unit.Env
import CSlash.Unit.Types
import CSlash.Unit.State
-- import GHC.Linker.MacOS
import CSlash.Linker.Unit
-- import GHC.Linker.External
import CSlash.Utils.Logger
import CSlash.Utils.TmpFs

import Control.Monad (when)
import System.FilePath

linkDynLib :: Logger -> TmpFs -> DynFlags -> UnitEnv -> [String] -> [UnitId] -> IO ()
linkDynLib logger tmpfs dflags0 unit_env o_files dep_packages = do error "linkDynLib"
