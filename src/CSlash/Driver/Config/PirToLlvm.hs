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
  version <- figureLlvmVersion logger dflags
  llvm_config <- readLlvmConfigCache config_cache
  pure $! LlvmCgConfig
    { llvmCgPlatform = targetPlatform dflags
    , llvmCgContext = initSDocContext dflags PprCode
    , llvmCgFillUndefWithGarbage = gopt Opt_LlvmFillUndefWithGarbage dflags
    , llvmCgSplitSection = gopt Opt_SplitSections dflags
    -- , llvmAvxEnabled= isAvxEnabled dflags
    -- , llvmCgBmiVersion = case platformArch (targetPlatform dflags) of
    --     ArchX86_64 -> bmiVersion dflags
    --     ArchUnknown -> Nothing
    , llvmCgLlvmVersion = version
    , llvmCgDoWarn = wopt Opt_WarnUnsupportedLlvmVersion dflags
    , llvmCgLlvmTarget = platformMisc_llvmTarget $! platformMisc dflags
    , llvmCgLlvmConfig = llvm_config
    }
