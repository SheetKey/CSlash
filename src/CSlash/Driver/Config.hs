module CSlash.Driver.Config where

import CSlash.Driver.DynFlags
import CSlash.Core.SimpleOpt
import CSlash.Core.Opt.Coercion

initOptCoercionOpts :: DynFlags -> OptCoercionOpts
initOptCoercionOpts dflags = OptCoercionOpts 
  { optCoercionEnabled = not (hasNoOptCoercion dflags) }

initSimpleOpts :: DynFlags -> SimpleOpts
initSimpleOpts dflags = SimpleOpts
  { so_uf_opts = unfoldingOpts dflags
  , so_co_opts = initOptCoercionOpts dflags
  , so_eta_red = gopt Opt_DoEtaReduction dflags
  }
