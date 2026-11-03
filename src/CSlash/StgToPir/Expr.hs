{-# LANGUAGE BangPatterns #-}

module CSlash.StgToPir.Expr (cgExpr{-, cgLit-}) where

-- import {-# SOURCE #-} GHC.StgToCmm.Bind ( cgBind )

import CSlash.StgToPir.Monad
-- import GHC.StgToCmm.Heap
import CSlash.StgToPir.Env
-- import GHC.StgToCmm.DataCon
-- import GHC.StgToCmm.Prof (saveCurrentCostCentre, restoreCurrentCostCentre, emitSetCCC)
import CSlash.StgToPir.Layout
-- import GHC.StgToCmm.Lit
import CSlash.StgToPir.Prim
-- import GHC.StgToCmm.Hpc
-- import GHC.StgToCmm.TagCheck
-- import GHC.StgToCmm.Ticky
-- import GHC.StgToCmm.Utils
import CSlash.StgToPir.Function

import CSlash.Stg.Syntax

import CSlash.Pir.Graph
import CSlash.Pir.BlockId
import CSlash.Pir hiding ( succ )
-- import CSlash.Pir.Info
-- import GHC.Cmm.Utils ( cmmTagMask, mkWordCLit, mAX_PTR_TAG )
import CSlash.Core
import CSlash.Core.DataCon
-- import GHC.Types.ForeignCall
import CSlash.Types.Var.Id
import CSlash.Types.Var.Class
import CSlash.Builtin.PrimOps
import CSlash.Core.TyCon
import CSlash.Types.RepType ( isZeroBitTy{-, countConRepArgs-}, mightBeFunTy )
-- import GHC.Types.CostCentre ( CostCentreStack, currentCCS )
import CSlash.Types.Tickish
import CSlash.Data.Maybe
import CSlash.Utils.Misc
import CSlash.Data.FastString
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Control.Monad ( unless, void )
import Control.Arrow ( first )
import Data.List     ( partition )
-- import GHC.Stg.InferTags.TagSig (isTaggedSig)
import CSlash.Platform.Profile (profileIsProfiling)

------------------------------------------------------------------------
--              cgExpr: the main function
------------------------------------------------------------------------

cgExpr :: CgStgExpr -> FCode ()

cgExpr (StgApp fun args) = cgIdApp fun args

cgExpr (StgOpApp op args ty) = cgOpApp op args ty

cgExpr e = pprPanic "cgExpr" (ppr e)

-----------------------------------------------------------------------------
--      Tail calls
-----------------------------------------------------------------------------

cgIdApp :: CoreId -> [StgArg] -> FCode ()
cgIdApp fun_id args = do
  platform <- getPlatform
  fun_info <- getCgIdInfo fun_id
  cfg <- getStgToPirConfig
  self_loop <- getSelfLoop
  let profile = stgToPirProfile cfg
      fun_arg = StgVarArg fun_id
      fun_name = varName fun_id
      fun = idInfoToAmode fun_info
      lf_info = cg_lf fun_info
      n_args = length args
  case getCallMethod cfg fun_name fun_id lf_info n_args (cg_loc fun_info) self_loop of
    DirectEntry lbl arity -> 
      -- nodeMustPointToIt
      directCall lbl arity args
    it -> pprPanic "unfinished" (ppr it)
