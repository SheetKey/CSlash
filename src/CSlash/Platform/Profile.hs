module CSlash.Platform.Profile where

import CSlash.Platform
import CSlash.Platform.Ways

data Profile = Profile
  { profilePlatform :: !Platform
  , profileWays :: !Ways
  }
  deriving (Eq, Ord, Show, Read)

profileBuildTag :: Profile -> String
profileBuildTag profile
  | platformUnregisterised platform = 'u':wayTag
  | otherwise = wayTag
  where
    platform = profilePlatform profile
    wayTag = waysBuildTag (profileWays profile)
