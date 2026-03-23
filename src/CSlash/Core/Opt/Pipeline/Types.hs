module CSlash.Core.Opt.Pipeline.Types where

import CSlash.Core ( CoreProgram )
-- import CSlash.Core.Opt.Monad ( CoreM, FloatOutSwitches )
import CSlash.Core.Opt.Simplify ( SimplifyOpts(..) )

import CSlash.Types.Basic  ( CompilerPhase(..) )
import CSlash.Unit.Module.ModGuts
import CSlash.Utils.Outputable as Outputable

{- *********************************************************************
*                                                                      *
              The CoreToDo type and related types
          Abstraction of core-to-core passes to run.
*                                                                      *
********************************************************************* -}

data CoreToDo
  = CoreDoSimplify !SimplifyOpts

  | CoreDesugar
  | CoreDesugarOpt

  | CoreTidy
  | CorePrep
