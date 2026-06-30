module CSlash.Driver.Config.StgToPir (initStgToPirConfig) where

import CSlash.StgToPir.Config

-- import GHC.Cmm.MachOp (FMASign(..))
import CSlash.Driver.Backend
import CSlash.Driver.Session
import CSlash.Platform
import CSlash.Platform.Profile
-- import GHC.Platform.Regs
import CSlash.Utils.Error
import CSlash.Unit.Module
import CSlash.Utils.Outputable

initStgToPirConfig :: DynFlags -> Module -> StgToPirConfig
initStgToPirConfig dflags mod = StgToPirConfig
  { stgToPirProfile = profile
  , stgToPirThisModule = mod
  , stgToPirTmpDir = tmpDir dflags
  , stgToPirContext = initSDocContext dflags defaultDumpStyle
  , stgToPirEmitDebugInfo = debugLevel dflags > 0
  ------------------------------ Ticky Options ----------------------------------
  , stgToPirDoTicky = False -- gopt Opt_Ticky dflags
  ---------------------------------- Flags --------------------------------------
  , stgToPirLoopification = gopt Opt_Loopification dflags
  , stgToPirAlignCheck = gopt Opt_AlignmentSanitisation dflags
  , stgToPirSCCProfiling = sccProfilingEnabled dflags
  , stgToPirPIC = gopt Opt_PIC dflags
  , stgToPirPIE = gopt Opt_PIE dflags
  , stgToPirExtDynRefs = gopt Opt_ExternalDynamicRefs dflags
  , stgToPirDoBoundsCheck = gopt Opt_DoBoundsChecking dflags
  , stgToPirObjectDeterminism = False -- gopt Opt_ObjectDeterminism dflags
  }
  where
    profile = targetProfile dflags
