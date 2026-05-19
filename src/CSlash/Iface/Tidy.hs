module CSlash.Iface.Tidy where

import CSlash.Tc.Types
import CSlash.Tc.Utils.Env

import CSlash.Core
import CSlash.Core.Unfold
-- import CSlash.Core.Unfold.Make
import CSlash.Core.FVs
-- import CSlash.Core.Tidy
import CSlash.Core.Seq         ( seqBinds )
import CSlash.Core.Opt.Arity   ( exprArity, typeArity{-, exprBotStrictness_maybe-} )
import CSlash.Core.Type
import CSlash.Core.DataCon
import CSlash.Core.TyCon
import CSlash.Core.Opt.OccurAnal ( occurAnalyzeExpr )

import CSlash.Iface.Env

import CSlash.Utils.Outputable
import CSlash.Utils.Misc( filterOut )
import CSlash.Utils.Panic
import CSlash.Utils.Logger as Logger
import qualified CSlash.Utils.Error as Err

-- import CSlash.Types.ForeignStubs
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Var
import CSlash.Types.Var.Id
-- import CSlash.Types.Var.Id.Make ( mkDictSelRhs )
import CSlash.Types.Var.Id.Info
import CSlash.Types.Demand  ( isDeadEndAppSig, {-isNopSig,-} nopSig, isDeadEndSig )
import CSlash.Types.Basic
import CSlash.Types.Name hiding (varName)
import CSlash.Types.Name.Set
import CSlash.Types.Name.Cache
import CSlash.Types.Avail
import CSlash.Types.Tickish
import CSlash.Types.TypeEnv
import CSlash.Tc.Utils.TcType (tcSplitNestedSigmaTys)

import CSlash.Unit.Module
import CSlash.Unit.Module.ModGuts
import CSlash.Unit.Module.ModDetails
import CSlash.Unit.Module.Deps

import CSlash.Data.Maybe

import Control.Monad
import Data.Function
import Data.List        ( sortBy, mapAccumL )
import qualified Data.Set as S
-- import CSlash.Types.CostCentre

data UnfoldingExposure
  = ExposeNone
  | ExposeSome
  | ExposeOverloaded
  | ExposeAll
  deriving (Show, Eq, Ord)

data TidyOpts = TidyOpts
  { opt_name_cache :: !NameCache
  , opt_collect_ccs :: !Bool
  , opt_unfolding_opts :: !UnfoldingOpts
  , opt_expose_unfoldings :: !UnfoldingExposure
  , opt_trim_ids :: !Bool
  , opt_expose_rules :: !Bool
  , opt_keep_auto_rules :: !Bool
  }
