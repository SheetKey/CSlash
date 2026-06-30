module CSlash.StgToPir.Config
  ( StgToPirConfig(..)
  , stgToPirPlatform
  ) where

import CSlash.Platform.Profile
import CSlash.Platform
import CSlash.Unit.Module
import CSlash.Utils.Outputable
import CSlash.Utils.TmpFs

-- import GHC.Cmm.MachOp ( FMASign(..) )

data StgToPirConfig = StgToPirConfig
  ----------------------------- General Settings --------------------------------
  { stgToPirProfile :: !Profile
  , stgToPirThisModule :: Module
  , stgToPirTmpDir :: !TempDir
  , stgToPirContext :: !SDocContext
  , stgToPirEmitDebugInfo :: !Bool
  ------------------------------ Ticky Options ----------------------------------
  , stgToPirDoTicky :: !Bool
  ---------------------------------- Flags --------------------------------------
  , stgToPirLoopification :: !Bool
  , stgToPirAlignCheck :: !Bool
  , stgToPirSCCProfiling :: !Bool
  , stgToPirPIC :: !Bool
  , stgToPirPIE :: !Bool
  , stgToPirExtDynRefs :: !Bool
  , stgToPirDoBoundsCheck :: !Bool
  , stgToPirObjectDeterminism :: !Bool
  {- We don't have backend flags since we only have LLVM backend.
     We don't hve SIMD flags since this is not yet supported.
  -}
  }

stgToPirPlatform :: StgToPirConfig -> Platform
stgToPirPlatform = profilePlatform . stgToPirProfile
