module CSlash.Driver.Config.Core.Opt.Simplify where

import CSlash.Core.Opt.Pipeline.Types ( CoreToDo(..) )
import CSlash.Core.Opt.Simplify ( {-SimplifyExprOpts(..), -}SimplifyOpts(..) )
import CSlash.Core.Opt.Simplify.Env ( FloatEnable(..), SimplMode(..) )
-- import CSlash.Core.Opt.Simplify.Monad ( TopEnvConfig(..) )

import CSlash.Driver.Config ( initOptCoercionOpts )
import CSlash.Driver.Config.Core.Lint ( initLintPassResultConfig )
-- import GHC.Driver.Config.Core.Opt.Arity ( initArityOpts )
import CSlash.Driver.DynFlags ( DynFlags(..), GeneralFlag(..), gopt )

import CSlash.Types.Basic ( CompilerPhase(..) )

import CSlash.Utils.Panic

initSimplifyOpts :: DynFlags -> Int -> SimplMode -> SimplifyOpts
initSimplifyOpts dflags iterations mode
  = let opts = SimplifyOpts
          { so_dump_core_sizes = not $ gopt Opt_SuppressCoreSizes dflags
          , so_iterations = iterations
          , so_mode = mode
          , so_pass_result_cfg = if gopt Opt_DoCoreLinting dflags
                                 then Just $ initLintPassResultConfig dflags (CoreDoSimplify opts)
                                 else Nothing
          }
    in opts

initSimplMode :: DynFlags -> CompilerPhase -> String -> SimplMode
initSimplMode dflags phase name = SimplMode

initGentleSimplMode :: DynFlags -> SimplMode
initGentleSimplMode dflags = --(initSimplMode dflags InitialPhase "Gentle")
  panic "{ sm_case_case = False }"
