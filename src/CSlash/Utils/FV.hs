{-# LANGUAGE BangPatterns #-}

module CSlash.Utils.FV where

import CSlash.Types.Var
import CSlash.Types.Var.Set

type InterestingVarFun = Var -> Bool

type FV = InterestingVarFun -> VarSet -> VarAcc -> VarAcc

type VarAcc = ([Var], VarSet)

fvVarAcc :: FV ->  ([Var], VarSet)
fvVarAcc fv = fv (const True) emptyVarSet ([], emptyVarSet)

fvVarList :: FV -> [Var]
fvVarList = fst . fvVarAcc

fvDVarSet :: FV -> DVarSet
fvDVarSet = mkDVarSet . fvVarList

fvVarSet :: FV -> VarSet
fvVarSet = snd . fvVarAcc

unitFV :: Id -> FV
unitFV var fv_cand in_scope acc@(have, haveSet)
  | var `elemVarSet` in_scope = acc
  | var `elemVarSet` haveSet = acc
  | fv_cand var = (var:have, extendVarSet haveSet var)
  | otherwise = acc
{-# INLINE unitFV #-}

emptyFV :: FV
emptyFV _ _ acc = acc
{-# INLINE emptyFV #-}

unionFV :: FV -> FV -> FV
unionFV fv1 fv2 fv_cand in_scope acc =
  fv1 fv_cand in_scope $! fv2 fv_cand in_scope $! acc
{-# INLINE unionFV #-}

delFV :: Var -> FV -> FV
delFV var fv fv_cand !in_scope acc =
  fv fv_cand (extendVarSet in_scope var) acc
{-# INLINE delFV #-}

delFVs :: VarSet -> FV -> FV
delFVs vars fv fv_cand !in_scope acc =
  fv fv_cand (in_scope `unionVarSet` vars) acc
{-# INLINE delFVs #-}

filterFV :: InterestingVarFun -> FV -> FV
filterFV fv_cand2 fv fv_cand1 in_scope acc =
  fv (\v -> fv_cand1 v && fv_cand2 v) in_scope acc
{-# INLINE filterFV #-}

mapUnionFV :: (a -> FV) -> [a] -> FV
mapUnionFV _f [] _fv_cand _in_scope acc = acc
mapUnionFV f (a:as) fv_cand in_scope acc =
  mapUnionFV f as fv_cand in_scope $! f a fv_cand in_scope $! acc
{-# INLINABLE mapUnionFV #-}

unionsFV :: [FV] -> FV
unionsFV fvs fv_cand in_scope acc = mapUnionFV id fvs fv_cand in_scope acc
{-# INLINE unionsFV #-}

mkFVs :: [Var] -> FV
mkFVs vars fv_cand in_scope acc =
  mapUnionFV unitFV vars fv_cand in_scope acc
{-# INLINE mkFVs #-}
