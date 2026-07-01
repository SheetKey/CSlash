module CSlash.Driver.Config.PirToLlvm (initLlvmCgConfig) where

import CSlash.Driver.DynFlags
import CSlash.Driver.LlvmConfigCache
import CSlash.Platform
import CSlash.PirToLlvm.Config
import CSlash.SysTools.Tasks

import CSlash.Utils.Outputable
import CSlash.Utils.Logger
import CSlash.Utils.Panic

initLlvmCgConfig :: Logger -> LlvmConfigCache -> DynFlags -> IO LlvmCgConfig
initLlvmCgConfig logger config_cache dflags = do
  panic "initLlvmCgConfig"
