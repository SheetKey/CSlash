module CSlash.Driver.Config.CoreToStg where

-- import CSlash.Driver.Config.Stg.Debug
import CSlash.Driver.DynFlags

import CSlash.CoreToStg

initCoreToStgOpts :: DynFlags -> CoreToStgOpts
initCoreToStgOpts dflags = CoreToStgOpts
  { coreToStg_platform = targetPlatform dflags
  , coreToStg_ways = ways dflags
  , coreToStg_ExternalDynamicRefs = gopt Opt_ExternalDynamicRefs dflags
  }
