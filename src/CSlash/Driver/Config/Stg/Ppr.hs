module CSlash.Driver.Config.Stg.Ppr (initStgPprOpts) where

import CSlash.Stg.Syntax

import CSlash.Driver.Session

initStgPprOpts :: DynFlags -> StgPprOpts
initStgPprOpts dflags = StgPprOpts
   { stgSccEnabled = sccProfilingEnabled dflags
   }
