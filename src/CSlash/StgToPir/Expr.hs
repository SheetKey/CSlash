module CSlash.StgToPir.Expr (cgExpr{-, cgLit-}) where

-- import {-# SOURCE #-} GHC.StgToCmm.Bind ( cgBind )

import CSlash.StgToPir.Monad
-- import GHC.StgToCmm.Heap
import CSlash.StgToPir.Env
-- import GHC.StgToCmm.DataCon
-- import GHC.StgToCmm.Prof (saveCurrentCostCentre, restoreCurrentCostCentre, emitSetCCC)
-- import GHC.StgToCmm.Layout
-- import GHC.StgToCmm.Lit
-- import GHC.StgToCmm.Prim
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
import CSlash.Builtin.PrimOps
import CSlash.Core.TyCon
import CSlash.Types.RepType ( isZeroBitTy{-, countConRepArgs, mightBeFunTy-} )
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
cgExpr = panic "cgExpr"


