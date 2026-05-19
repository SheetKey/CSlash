{-# LANGUAGE MultiWayIf #-}

module CSlash.Driver.Config.Tidy (initTidyOpts) where

import CSlash.Iface.Tidy
-- import CSlash.Iface.Tidy.StaticPtrTable

import CSlash.Driver.DynFlags
import CSlash.Driver.Env
import CSlash.Driver.Backend

-- import GHC.Core.Make (getMkStringIds)
import CSlash.Builtin.Names
import CSlash.Tc.Utils.Env (lookupGlobal)
import CSlash.Types.TyThing
import CSlash.Platform.Ways

import CSlash.Utils.Panic

initTidyOpts :: CsEnv -> IO TidyOpts
initTidyOpts cs_env = do
  let dflags = cs_dflags cs_env
  pure $ TidyOpts
    { opt_name_cache = cs_NC cs_env
    , opt_collect_ccs = ways dflags `hasWay` WayProf
    , opt_unfolding_opts = unfoldingOpts dflags
    , opt_expose_unfoldings = if | gopt Opt_OmitInterfacePragmas dflags -> ExposeNone
                                 | gopt Opt_ExposeAllUnfoldings dflags -> ExposeAll
                                 | panic "gopt Opt_ExposeOverloadedUnfoldings dflags" -> ExposeOverloaded
                                 | otherwise -> ExposeSome
    , opt_expose_rules = not (gopt Opt_OmitInterfacePragmas dflags)
    , opt_trim_ids = gopt Opt_OmitInterfacePragmas dflags
    , opt_keep_auto_rules = panic "gopt Opt_KeepAutoRules dflags"
    }

