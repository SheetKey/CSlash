module CSlash.Core.Opt.Simplify where

import CSlash.Driver.Flags

import CSlash.Core
import CSlash.Core.Ppr     ( pprCoreBindings, pprCoreExpr )
-- import CSlash.Core.Opt.OccurAnal ( occurAnalysePgm, occurAnalyseExpr )
-- import CSlash.Core.Stats   ( coreBindsSize, coreBindsStats, exprSize )
-- import CSlash.Core.Utils   ( mkTicks, stripTicksTop )
import CSlash.Core.Lint    ( LintPassResultConfig, dumpPassResult, lintPassResult )
-- import CSlash.Core.Opt.Simplify.Iteration ( simplTopBinds, simplExpr, simplImpRules )
-- import CSlash.Core.Opt.Simplify.Utils  ( activeRule )
-- import CSlash.Core.Opt.Simplify.Inline ( activeUnfolding )
import CSlash.Core.Opt.Simplify.Env
-- import CSlash.Core.Opt.Simplify.Monad
-- import CSlash.Core.Opt.Stats ( simplCountN )

import CSlash.Utils.Error  ( withTiming )
import CSlash.Utils.Logger as Logger
import CSlash.Utils.Outputable
import CSlash.Utils.Constants (debugIsOn)

-- import CSlash.Unit.Env ( UnitEnv, ueEPS )
import CSlash.Unit.External
import CSlash.Unit.Module.ModGuts

import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Basic
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.Tickish
import CSlash.Types.Unique.FM

import Control.Monad
import Data.Foldable ( for_ )

{- *********************************************************************
*                                                                      *
        Gentle simplification
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
            The driver for the simplifier
*                                                                      *
********************************************************************* -}

data SimplifyOpts = SimplifyOpts
  { so_dump_core_sizes :: !Bool
  , so_iterations :: !Int
  , so_mode :: !SimplMode
  , so_pass_result_cfg :: !(Maybe LintPassResultConfig)
  -- , so_top_env_cfg :: !TopEnvConfig
  }
