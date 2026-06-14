module CSlash.Stg.Make where

import CSlash.Core (CoreId, CoreDataCon, CoreType)

import CSlash.Unit.Module

import CSlash.Core.DataCon
import CSlash.Core.Type (Type)

import CSlash.Stg.Syntax
import CSlash.Stg.Utils (stripStgTicksTop)

import CSlash.Types.Var.Id
import CSlash.Types.Name
-- import CSlash.Types.CostCentre
-- import CSlash.Types.Demand ( isAtMostOnceDmd )
import CSlash.Types.Tickish

import CSlash.Utils.Panic

data MkStgRhs = MkStgRhs
  { rhs_args :: [CoreId]
  , rhs_expr :: StgExpr
  , rhs_type :: CoreType
  , rhs_is_join :: !Bool
  }

mkTopStgRhs
  :: (Module -> CoreDataCon -> [StgArg] -> Bool)
  -> Module -> CoreId -> MkStgRhs -> StgRhs
mkTopStgRhs allow_toplevel_con_app this_mod bndr mk_rhs@(MkStgRhs bndrs rhs ty _)
  | Just rhs_con <- mkTopStgRhsCon_maybe (allow_toplevel_con_app this_mod) mk_rhs
  = rhs_con

  | not (null bndrs)
  = StgRhsClosure noExtFieldSilent bndrs rhs ty

  | otherwise
  = StgRhsClosure noExtFieldSilent [] rhs ty

mkStgRhs :: CoreId -> MkStgRhs -> StgRhs
mkStgRhs bndr mk_rhs@(MkStgRhs bndrs rhs ty is_join)
  | Just rhs_con <- mkStgRhsCon_maybe mk_rhs
  = rhs_con
  | otherwise
  = StgRhsClosure noExtFieldSilent bndrs rhs ty

mkStgRhsCon_maybe :: MkStgRhs -> Maybe StgRhs
mkStgRhsCon_maybe (MkStgRhs bndrs rhs ty is_join)
  | [] <- bndrs
  , not is_join
  , (ticks, StgConApp con mn args) <- stripStgTicksTop (not . tickishIsCode) rhs
  = Just (StgRhsCon con mn ticks args ty)
  | otherwise
  = Nothing

mkTopStgRhsCon_maybe :: (CoreDataCon -> [StgArg] -> Bool) -> MkStgRhs -> Maybe StgRhs
mkTopStgRhsCon_maybe allow_static_con_app (MkStgRhs bndrs rhs ty is_join)
  | [] <- bndrs
  , not is_join
  , (ticks, StgConApp con mn args) <- stripStgTicksTop (not . tickishIsCode) rhs
  , allow_static_con_app con args
  = Just (StgRhsCon con mn ticks args ty)
  | otherwise
  = Nothing
