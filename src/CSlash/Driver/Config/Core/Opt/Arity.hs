module CSlash.Driver.Config.Core.Opt.Arity where

import CSlash.Driver.DynFlags

import CSlash.Core.Opt.Arity

initArityOpts :: DynFlags -> ArityOpts
initArityOpts dflags = ArityOpts
  -- { ao_ped_bot = gopt Opt_PedanticBottoms dflags
  -- , ao_dicts_cheap = gopt Opt_DictsCheap dflags
  -- }
