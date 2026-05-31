module CSlash.Driver.Config.Core.Opt.LiberateCase where

import CSlash.Driver.DynFlags

import CSlash.Core.Opt.LiberateCase ( LibCaseOpts(..) )

initLiberateCaseOpts :: DynFlags -> LibCaseOpts
initLiberateCaseOpts dflags = LibCaseOpts
  { lco_threshold = liberateCaseThreshold dflags
  , lco_unfolding_opts = unfoldingOpts dflags
  }
