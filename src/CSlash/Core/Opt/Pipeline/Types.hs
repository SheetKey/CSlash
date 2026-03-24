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

instance Outputable CoreToDo where
  ppr (CoreDoSimplify _) = text "Simplifier"
  ppr CoreDesugar = text "Desugar (before optimization)"
  ppr CoreDesugarOpt = text "Desugar (after optimization)"
  ppr CoreTidy = text "Tidy Core"
  ppr CorePrep = text "CorePrep"

pprPassDetails :: CoreToDo -> SDoc
pprPassDetails (CoreDoSimplify cfg) = vcat [ text "Max iterations =" <+> int n
                                           , ppr md ]
  where
    n = so_iterations cfg
    md = so_mode cfg
pprPassDetails _ = Outputable.empty
