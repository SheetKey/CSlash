module CSlash.Driver.Config.CoreToStg.Prep where

import CSlash.Core.Opt.Pipeline.Types ( CoreToDo(..) )
import CSlash.Driver.Env
import CSlash.Driver.Session
import CSlash.Driver.Config.Core.Lint
import CSlash.Driver.Config.Core.Opt.Arity
import CSlash.Types.Var
import CSlash.Utils.Outputable ( alwaysQualify )

import CSlash.CoreToStg.Prep

initCorePrepConfig :: CsEnv -> IO CorePrepConfig
initCorePrepConfig cs_env = do
  let dflags = cs_dflags cs_env
  return $ CorePrepConfig
    { cp_catchNonexhaustiveCases = gopt Opt_CatchNonexhaustiveCases dflags
    , cp_platform = targetPlatform dflags
    , cp_arityOpts = if gopt Opt_DoCleverArgEtaExpansion dflags
                     then Just (initArityOpts dflags)
                     else Nothing
    , cp_specEval = gopt Opt_SpecEval dflags
    }

initCorePrepPgmConfig :: DynFlags -> CorePrepPgmConfig
initCorePrepPgmConfig dflags = CorePrepPgmConfig
  { cpPgm_endPassConfig = initEndPassConfig dflags alwaysQualify CorePrep
  , cpPgm_generateDebugInfo = needSourceNotes dflags
  }
