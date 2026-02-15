module CSlash.Core.SimpleOpt where

import CSlash.Core
-- import CSlash.Core.Opt.Arity
import CSlash.Core.Subst
import CSlash.Core.Utils
-- import CSlash.Core.FVs
import CSlash.Core.Unfold
-- import CSlash.Core.Unfold.Make
-- import CSlash.Core.Make ( FloatBind(..) )
-- import CSlash.Core.Opt.OccurAnal( occurAnalyseExpr, occurAnalysePgm, zapLambdaBndrs )
import CSlash.Core.DataCon
-- import CSlash.Core.Coercion.Opt ( optCoercion, OptCoercionOpts (..) )
import CSlash.Core.Type
import CSlash.Core.Predicate( isTyCoVarType )

import CSlash.Types.Literal
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info ( realUnfoldingInfo, setUnfoldingInfo, setRuleInfo, IdInfo (..) )
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.Demand( etaConvertDmdSig, topSubDmd )
import CSlash.Types.Tickish
import CSlash.Types.Basic

import CSlash.Builtin.Types
import CSlash.Builtin.Names

import CSlash.Unit.Module ( Module )
import CSlash.Utils.Encoding
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc

import CSlash.Data.Maybe       ( orElse )
-- import CSlash.Data.Graph.UnVar
import Data.List (mapAccumL)
import qualified Data.ByteString as BS


{- *********************************************************************
*                                                                      *
        The Simple Optimiser
*                                                                      *
********************************************************************* -}

data SimpleOpts = SimpleOpts
  { so_uf_opts :: !UnfoldingOpts
  -- TODO: , so_co_opts :: !OptCoercionOpts
  , so_eta_red :: !Bool
  , so_inline :: !Bool
  }
