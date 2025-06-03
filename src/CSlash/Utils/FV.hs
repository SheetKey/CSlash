{-# LANGUAGE BangPatterns #-}

module CSlash.Utils.FV where

import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Types.Unique

type InterestingVarFun v = v -> Bool

type FV v = InterestingVarFun v -> MkVarSet v -> MkVarAcc v -> MkVarAcc v

type MkVarAcc v = ([v], MkVarSet v)

fvVarAcc :: FV v ->  ([v], MkVarSet v)
fvVarAcc fv = fv (const True) emptyVarSet ([], emptyVarSet)

fvVarList :: FV v -> [v]
fvVarList = fst . fvVarAcc

fvDVarSet :: Uniquable v => FV v -> MkDVarSet v
fvDVarSet = mkDVarSet . fvVarList

fvVarSet :: FV v -> MkVarSet v
fvVarSet = snd . fvVarAcc

unitFV :: Uniquable v => v -> FV v
unitFV var fv_cand in_scope acc@(have, haveSet)
  | var `elemVarSet` in_scope = acc
  | var `elemVarSet` haveSet = acc
  | fv_cand var = (var:have, extendVarSet haveSet var)
  | otherwise = acc
{-# INLINE unitFV #-}

emptyFV :: FV v
emptyFV _ _ acc = acc
{-# INLINE emptyFV #-}

unionFV :: FV v -> FV v -> FV v
unionFV fv1 fv2 fv_cand in_scope acc =
  fv1 fv_cand in_scope $! fv2 fv_cand in_scope $! acc
{-# INLINE unionFV #-}

delFV :: Uniquable v => v -> FV v -> FV v
delFV var fv fv_cand !in_scope acc =
  fv fv_cand (extendVarSet in_scope var) acc
{-# INLINE delFV #-}

delFVs :: MkVarSet v -> FV v -> FV v
delFVs vars fv fv_cand !in_scope acc =
  fv fv_cand (in_scope `unionVarSet` vars) acc
{-# INLINE delFVs #-}

filterFV :: InterestingVarFun v -> FV v -> FV v
filterFV fv_cand2 fv fv_cand1 in_scope acc =
  fv (\v -> fv_cand1 v && fv_cand2 v) in_scope acc
{-# INLINE filterFV #-}

mapUnionFV :: (a -> FV v) -> [a] -> FV v
mapUnionFV _f [] _fv_cand _in_scope acc = acc
mapUnionFV f (a:as) fv_cand in_scope acc =
  mapUnionFV f as fv_cand in_scope $! f a fv_cand in_scope $! acc
{-# INLINABLE mapUnionFV #-}

unionsFV :: [FV v] -> FV v
unionsFV fvs fv_cand in_scope acc = mapUnionFV id fvs fv_cand in_scope acc
{-# INLINE unionsFV #-}

mkFVs :: Uniquable v => [v] -> FV v
mkFVs vars fv_cand in_scope acc =
  mapUnionFV unitFV vars fv_cand in_scope acc
{-# INLINE mkFVs #-}
