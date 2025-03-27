{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}

module CSlash.Core.Kind.Compare where

import CSlash.Core.Kind
import CSlash.Core.Kind.FVs

import CSlash.Core.Type.Rep
import CSlash.Core.Type.FVs
import CSlash.Core.TyCon

import CSlash.Types.Var
import CSlash.Types.Unique
import CSlash.Types.Var.Env

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic

import GHC.Base (reallyUnsafePtrEquality#)

import qualified Data.Semigroup as S

{- *********************************************************************
*                                                                      *
            Kind equality
*                                                                      *
********************************************************************* -}

tcEqKind :: HasDebugCallStack => Kind -> Kind -> Bool
tcEqKind orig_ki1 orig_ki2 = go orig_env orig_ki1 orig_ki2
  where
    go :: RnEnv2 -> Kind -> Kind -> Bool
    go _ UKd UKd = True
    go _ AKd AKd = True
    go _ LKd LKd = True
    go env (KiVarKi kv1) (KiVarKi kv2)
      = rnOccL env kv1 == rnOccR env kv2
    go env (FunKd _ arg1 res1) (FunKd _ arg2 res2)
      = go env arg1 arg2 && go env res1 res2
    go env (KdContext rels1) (KdContext rels2)
      = all2 (go_rel env) rels1 rels2
    go _ _ _ = False

    go_rel env (LTKd k1 k2) (LTKd k1' k2')
      = go env k1 k1' && go env k2 k2'
    go_rel env (LTEQKd k1 k2) (LTEQKd k1' k2')
      = go env k1 k1' && go env k2 k2'
    go_rel _ _ _ = False

    orig_env = mkRnEnv2 $ mkInScopeSet $ kiVarsOfKinds [orig_ki1, orig_ki2]

{- *********************************************************************
*                                                                      *
                Comparison for kinds
*                                                                      *
********************************************************************* -}

eqKind :: Kind -> Kind -> Bool
eqKind k1 k2 = isEqual $ nonDetCmpKind k1 k2

nonDetCmpKind :: Kind -> Kind -> Ordering
nonDetCmpKind !k1 !k2
  | 1# <- reallyUnsafePtrEquality# k1 k2
  = EQ
nonDetCmpKind k1 k2 = nonDetCmpKindX rn_env k1 k2
  where
    rn_env = mkRnEnv2 (mkInScopeSet (kiVarsOfKinds [k1, k2]))
{-# INLINE nonDetCmpKind #-}

nonDetCmpKindX :: RnEnv2 -> Kind -> Kind -> Ordering
nonDetCmpKindX env orig_k1 orig_k2 = go env orig_k1 orig_k2
  where
    go :: RnEnv2 -> Kind -> Kind -> Ordering
    go _ UKd UKd = EQ
    go _ AKd AKd = EQ
    go _ LKd LKd = EQ
    -- go UKd AKd = LT
    -- go UKd LKd = LT
    -- go AKd LKd = LT
    -- go AKd UKd = GT
    -- go LKd AKd = GT
    -- go LKd
    go env (KiVarKi kv1) (KiVarKi kv2)
      = rnOccL env kv1 `nonDetCmpVar` rnOccR env kv2
    go env (FunKd _ a1 r1) (FunKd _ a2 r2)
      = nonDetCmpKindX env a1 a2 S.<> nonDetCmpKindX env r1 r2
    -- go env (KdContext rels1) (KdContext rels2) = go_rels env rels1 rels2
    go _ k1 k2 = get_rank k1 `compare` get_rank k2
      where
        get_rank :: Kind -> Int
        get_rank (KiVarKi {}) = 0
        get_rank UKd = 1
        get_rank AKd = 2
        get_rank LKd = 3
        get_rank (KdContext {}) = 4
        get_rank (FunKd {}) = 5

    {- NOTE: Comparing contexts is very hard.
             What if we have 'go_rels env [r1, r2] [r2, r1]'?
             What if the number of rels mismatch?
             What if we have 'go_rel (LTKd k1 AKd) (LTEQKd k1 AKd)?
             Tough!
    -}

    -- go_rels :: RnEnv2 -> [KdRel] -> [KdRel] -> Ordering
    -- go_rels _ _ _ = EQ
    -- go_rels env rels1 rels2 = foldr1 (S.<>) $ zipWith (go_rel env) rels1 rels2

    -- go_rel env (LTKd lk1 lk2) (LTKd rk1 rk2) = go env lk1 rk1 || go env lk2 rk2
    -- go_rel env (LTEQKd lk1 lk2) (LTEQKd rk1 rk2) = go env lk1 rk1 || go env lk2 rk2
    -- go_rel _ (LTKd _ _) (LTEQKd _ _) = LT
    -- go_rel _ (LTEQKd _ _) (LTKd _ _) = GT

