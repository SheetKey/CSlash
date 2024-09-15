module CSlash.Driver.Config.Logger (initLogFlags) where

import CSlash.Driver.DynFlags

import CSlash.Utils.Logger (LogFlags (..))
import CSlash.Utils.Outputable

initLogFlags :: DynFlags -> LogFlags
initLogFlags dflags = LogFlags
  { log_default_user_context = initSDocContext dflags defaultUserStyle
  , log_default_dump_context = initSDocContext dflags defaultDumpStyle
  , log_dump_flags           = dumpFlags dflags
  , log_show_caret           = gopt Opt_DiagnosticsShowCaret dflags
  , log_show_warn_groups     = gopt Opt_ShowWarnGroups dflags
  , log_enable_timestamps    = not (gopt Opt_SuppressTimestamps dflags)
  , log_dump_to_file         = gopt Opt_DumpToFile dflags
  , log_dump_dir             = dumpDir dflags
  , log_dump_prefix          = dumpPrefix dflags
  , log_dump_prefix_override = dumpPrefixForce dflags
  , log_with_ways            = gopt Opt_DumpWithWays dflags
  , log_enable_debug         = not (hasNoDebugOutput dflags)
  , log_verbosity            = verbosity dflags
  , log_ways                 = Just $ ways dflags
  }
