module CSlash.Driver.Config.Core.Rules (initRuleOpts) where

import CSlash.Driver.Flags
import CSlash.Driver.DynFlags ( DynFlags, gopt, targetPlatform, homeUnitId_ )

import CSlash.Core.Rules.Config

-- import GHC.Unit.Types     ( primUnitId, bignumUnitId )

initRuleOpts :: DynFlags -> RuleOpts
initRuleOpts dflags = RuleOpts
  { roPlatform = targetPlatform dflags
  , roNumConstantFolding = gopt Opt_NumConstantFolding dflags
  , roExcessRationalPrecision = gopt Opt_ExcessPrecision dflags
  }
