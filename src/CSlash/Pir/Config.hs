module CSlash.Pir.Config where

import CSlash.Platform
import CSlash.Platform.Profile

data PirConfig = PirConfig
  { pirProfile :: !Profile
  , pirOptControlFlow :: !Bool
  , pirDoLinting :: !Bool
  , pirOptElimCommonBlks :: !Bool
  , pirExternalDynamicRefs :: !Bool
  }

pirPlatform :: PirConfig -> Platform
pirPlatform = profilePlatform . pirProfile
