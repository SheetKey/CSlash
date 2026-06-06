module CSlash.Stg.Lift.Types where

import CSlash.Core (CoreId)
import CSlash.Types.Var.Id
import CSlash.Types.Demand
import CSlash.Types.Var.Set

import CSlash.Utils.Outputable

data Skeleton
  = ClosureSK !CoreId !DCoreIdSet !Skeleton
  | RhsSk !Card !Skeleton
  | AltSk !Skeleton !Skeleton
  | BothSk !Skeleton !Skeleton
  | NilSk

data BinderInfo
  = BindsClosure !CoreId !Bool
  | BoringBinder !CoreId
