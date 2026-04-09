module CSlash.Core.Rules.Config where

import CSlash.Platform

data RuleOpts = RuleOpts
  { roPlatform :: !Platform
  , roNumConstantFolding :: !Bool
  , roExcessRationalPrecision :: !Bool
  }
