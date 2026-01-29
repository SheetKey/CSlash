{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Utils.FV where

-- type FV arg is acc = (arg -> Bool) -> is -> acc -> acc
type FV thing
  = (FVArg thing -> Bool) -> FVInScope thing -> FVAcc thing -> FVAcc thing

class HasFVs thing where
  type FVInScope thing = r | r -> thing
  type FVAcc thing = r | r -> thing
  type FVArg thing

  fvElemAcc :: FVArg thing -> FVAcc thing -> Bool
  fvElemIS :: FVArg thing -> FVInScope thing -> Bool

  fvExtendAcc :: FVArg thing -> FVAcc thing -> FVAcc thing
  fvExtendIS :: FVArg thing -> FVInScope thing -> FVInScope thing

  fvEmptyAcc :: FVAcc thing
  fvEmptyIS :: FVInScope thing

fvVarAcc :: HasFVs thing => FV thing -> FVAcc thing
fvVarAcc fv = fv (const True) fvEmptyIS fvEmptyAcc

unitFV :: HasFVs thing => FVArg thing -> FV thing
unitFV var fv_cand in_scope acc
  | var `fvElemIS` in_scope = acc
  | var `fvElemAcc` acc = acc
  | fv_cand var = var `fvExtendAcc` acc
  | otherwise = acc
{-# INLINE unitFV #-}

emptyFV :: FV thing
emptyFV _ _ acc = acc
{-# INLINE emptyFV #-}

unionFV :: HasFVs thing => FV thing -> FV thing -> FV thing
unionFV fv1 fv2 fv_cand in_scope acc =
  fv1 fv_cand in_scope $! fv2 fv_cand in_scope $! acc
{-# INLINE unionFV #-}

delFV :: HasFVs thing => FVArg thing -> FV thing -> FV thing
delFV var fv fv_cand !in_scope acc =
  fv fv_cand (fvExtendIS var in_scope) acc
{-# INLINE delFV #-}

-- delFVs :: MkVarSet v -> FV v -> FV v
-- delFVs vars fv fv_cand !in_scope acc =
--   fv fv_cand (in_scope `unionVarSet` vars) acc
-- {-# INLINE delFVs #-}

filterFV :: HasFVs thing => (FVArg thing -> Bool) -> FV thing -> FV thing
filterFV fv_cand2 fv fv_cand1 in_scope acc =
  fv (\v -> fv_cand1 v && fv_cand2 v) in_scope acc
{-# INLINE filterFV #-}

mapUnionFV :: HasFVs thing => (a -> FV thing) -> [a] -> FV thing
mapUnionFV _f [] _fv_cand _in_scope acc = acc
mapUnionFV f (a:as) fv_cand in_scope acc =
  mapUnionFV f as fv_cand in_scope $! f a fv_cand in_scope $! acc
{-# INLINABLE mapUnionFV #-}

unionsFV :: HasFVs thing => [FV thing] -> FV thing
unionsFV fvs fv_cand in_scope acc = mapUnionFV id fvs fv_cand in_scope acc
{-# INLINE unionsFV #-}

mkFVs :: HasFVs thing => [FVArg thing] -> FV thing
mkFVs vars fv_cand in_scope acc =
  mapUnionFV unitFV vars fv_cand in_scope acc
{-# INLINE mkFVs #-}
