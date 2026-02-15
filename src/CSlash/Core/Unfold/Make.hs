module CSlash.Core.Unfold.Make where

import CSlash.Core
import CSlash.Core.Unfold
-- import CSlash.Core.Opt.OccurAnal ( occurAnalyseExpr )
-- import CSlash.Core.Opt.Arity   ( manifestArity )
import CSlash.Core.DataCon
import CSlash.Core.Utils
import CSlash.Types.Basic
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Demand ( DmdSig, isDeadEndSig )

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic

import Data.Maybe ( fromMaybe )

-- the very simple optimiser is used to optimise unfoldings
-- import {-# SOURCE #-} GHC.Core.SimpleOpt

mkInlineUnfoldingWithArity :: SimpleOpts -> UnfoldingSource -> Arity -> CoreExpr -> Unfolding
mkInlineUnfoldingWithArity opts src arity expr
  = mkCoreUnfolding src True expr' Nothing guide
  where
    expr' = simpleOptExpr opts expr
    guie = UnfWhen { ug_arity = arity
                   , ug_unsat_ok = needSaturated
                   , ug_boring_ok = boring_ok }

  boring_ok | arity == 0 = True
            | otherwise = inlineBoringOk expr'

mkInlinableUnfolding :: SimpleOpts -> UnfoldingSource -> CoreExpr -> Unfolding
mkInlinableUnfolding opts src expr
  = mkUnfolding (so_uf_opts opts) src False False False expr' Nothing
  where
    expr' = simpleOptExpr opts expr

mkUnfolding
  :: UnfoldingOpts
  -> UnfoldingSource
  -> Bool
  -> Bool
  -> Bool
  -> CoreExpr
  -> Maybe UnfoldingCache
  -> Unfolding
mkUnfolding opts src top_lvl is_bottoming is_join expr cache
  = mkCoreUnfolding src top_lvl expr cache guidance
  where
    is_top_bottoming = top_lvl && is_bottoming
    guidance = calcUnfoldingGuidance opts is_top_bottoming is_join expr

mkCoreUnfolding :: UnfoldingSouce
  -> Bool
  -> CoreExpr
  -> Maybe UnfoldingCache
  -> UnfoldingGuidance
  -> Unfolding
mkCoreUnfolding stc top_lvl expr precomputed_cache guidance
  = CoreUnfolding { uf_tmpl = cache `seq` occurAnalyseExpr expr
                  , uf_src = src
                  , uf_is_top = top_lvl
                  , uf_cache = cache
                  , uf_guidance = guidance }
  where
    is_value = exprIsHNF expr
    is_conlike = exprIsConLike expr
    is_work_free = exprIsWorkFree expr
    is_expandable = exprIsExpandable expr

    unfinished
