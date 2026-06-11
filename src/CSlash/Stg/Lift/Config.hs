module CSlash.Stg.Lift.Config (StgLiftConfig(..)) where

import CSlash.Platform.Profile

data StgLiftConfig = StgLiftConfig
  { c_targetProfile         :: !Profile
  , c_liftLamsRecArgs       :: !(Maybe Int)
  , c_liftLamsNonRecArgs    :: !(Maybe Int)
  , c_liftLamsKnown         :: !Bool
  }
  deriving (Show, Read, Eq, Ord)
