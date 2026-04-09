module CSlash.Core.Opt.Pipeline.Types where

import Prelude hiding ((<>))

import CSlash.Core ( CoreProgram )
import CSlash.Core.Opt.Monad ( CoreM, FloatOutSwitches )
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
  | CoreDoFloatInwards
  | CoreDoFloatOutwards FloatOutSwitches
  | CoreLiberateCase
  | CoreDoStaticArgs
  | CoreDoCallArity
  | CoreDoExitify
  | CoreDoDemand

  | CoreDoSpecializing
  | CoreDoSpecConstr
  | CoreCSE
  | CoreDoRuleCheck CompilerPhase String

  | CoreDoNothing
  | CoreDoPasses [CoreToDo]

  | CoreDesugar
  | CoreDesugarOpt

  | CoreTidy
  | CorePrep
  | CoreAddCallerCcs
  | CoreAddLateCcs

instance Outputable CoreToDo where
  ppr (CoreDoSimplify _) = text "Simplifier"
  ppr CoreDoFloatInwards = text "Float inwards"
  ppr (CoreDoFloatOutwards f) = text "Float out" <> parens (ppr f)
  ppr CoreLiberateCase = text "Liberate case"
  ppr CoreDoStaticArgs = text "Static argument"
  ppr CoreDoCallArity = text "Called arity analysis"
  ppr CoreDoExitify = text "Exitification transformation"
  ppr CoreDoDemand = text "Demand analysis"
  ppr CoreDoSpecializing = text "Specialize"
  ppr CoreDoSpecConstr = text "SpecConstr"
  ppr CoreCSE = text "Common sub-expression"
  ppr CoreDoNothing = text "CoreDoNothing"
  ppr (CoreDoPasses passes) = text "CoreDoPasses" <+> ppr passes
  ppr CoreDesugar = text "Desugar (before optimization)"
  ppr CoreDesugarOpt = text "Desugar (after optimization)"
  ppr CoreTidy = text "Tidy Core"
  ppr CorePrep = text "CorePrep"
  ppr CoreDoRuleCheck{} = text "Rule check"
  ppr CoreAddCallerCcs = text "Add caller cost-centers"
  ppr CoreAddLateCcs = text "Add late core cost-centers"

pprPassDetails :: CoreToDo -> SDoc
pprPassDetails (CoreDoSimplify cfg) = vcat [ text "Max iterations =" <+> int n
                                           , ppr md ]
  where
    n = so_iterations cfg
    md = so_mode cfg
pprPassDetails _ = Outputable.empty
