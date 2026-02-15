module CSlash.Driver.Config where

import CSlash.Driver.DynFlags
import CSlash.Core.SimpleOpt
-- import CSlash.Core.Coercion.Opt

initSimpleOpts :: DynFlags -> SimpleOpts
initSimpleOpts dflags = SimpleOpts
  { so_uf_opts = unfoldingOpts dflags
  , so_eta_red = gopt Opt_DoEtaReduction dflags
  , so_inline = True
  }
