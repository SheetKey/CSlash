{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}

module CSlash.Core.Kind.Compare where

import CSlash.Core.Kind
import CSlash.Core.Kind.FVs

import CSlash.Core.Type.Rep
import CSlash.Core.Type.FVs
import CSlash.Core.TyCon

import CSlash.Types.Var
import CSlash.Types.Var.Set
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

tcEqKind :: (HasDebugCallStack, IsVar kv) => Kind kv -> Kind kv -> Bool
tcEqKind = eqKind

tcEqMonoKind :: (HasDebugCallStack, IsVar kv) => MonoKind kv -> MonoKind kv -> Bool
tcEqMonoKind = eqMonoKind

initRnEnv :: IsVar kv => Kind kv -> Kind kv -> RnEnv2 kv
initRnEnv ka kb = mkRnEnv2 $ mkInScopeSet $
                  varsOfKind ka `unionVarSet` varsOfKind kb

eqKind :: (HasCallStack, IsVar kv) => Kind kv -> Kind kv -> Bool
eqKind ka kb = eq_kind ka kb

eqMonoKind :: (HasCallStack, IsVar kv) => MonoKind kv -> MonoKind kv -> Bool
eqMonoKind ka kb = eq_mono_kind ka kb

eq_kind :: IsVar kv => Kind kv -> Kind kv -> Bool
eq_kind = inline_generic_eq_kind_x Nothing

eq_mono_kind :: IsVar kv => MonoKind kv -> MonoKind kv -> Bool
eq_mono_kind = inline_generic_eq_mono_kind_x Nothing

{-# NOINLINE generic_eq_kind_x #-}
generic_eq_kind_x :: IsVar kv => Maybe (RnEnv2 kv) -> Kind kv -> Kind kv -> Bool
generic_eq_kind_x = inline_generic_eq_kind_x

{-# INLINE inline_generic_eq_kind_x #-}
inline_generic_eq_kind_x
  :: IsVar kv
  => Maybe (RnEnv2 kv) -> (Kind kv) -> (Kind kv) -> Bool
inline_generic_eq_kind_x mb_env = \k1 k2 -> k1 `seq` k2 `seq`
  let go = generic_eq_kind_x mb_env
      go_mono = generic_eq_mono_kind_x mb_env
  in case (k1, k2) of
       (Mono k1, Mono k2) -> go_mono k1 k2
       (ForAllKi kv1 body1, ForAllKi kv2 body2)
         -> case mb_env of
              Nothing -> generic_eq_kind_x (Just (initRnEnv k1 k2)) k1 k2
              Just env -> generic_eq_kind_x (Just (rnBndr2 env kv1 kv2)) body1 body2
       _ -> False

{-# NOINLINE generic_eq_mono_kind_x #-}
generic_eq_mono_kind_x
  :: (Eq kv, VarHasUnique kv) => Maybe (RnEnv2 kv) -> (MonoKind kv) -> (MonoKind kv) -> Bool
generic_eq_mono_kind_x = inline_generic_eq_mono_kind_x

{-# INLINE inline_generic_eq_mono_kind_x #-}
inline_generic_eq_mono_kind_x
  :: (VarHasUnique kv, Eq kv)
  => Maybe (RnEnv2 kv) -> (MonoKind kv) -> (MonoKind kv) -> Bool
inline_generic_eq_mono_kind_x mb_env = \k1 k2 -> k1 `seq` k2 `seq`
  let go = generic_eq_mono_kind_x mb_env
  in case (k1, k2) of
       _ | 1# <- reallyUnsafePtrEquality# k1 k2 -> True

       (KiPredApp p1 ka1 kb1, KiPredApp p2 ka2 kb2)
         | p1 == p2
           -> go ka1 ka2 && go kb1 kb2
         | otherwise
           -> False

       (BIKi k1, BIKi k2) -> k1 == k2
           
       (KiVarKi kv1, KiVarKi kv2)
         -> case mb_env of
              Nothing -> kv1 == kv2
              Just env -> rnOccL env kv1 == rnOccR env kv2

       (FunKi _ arg1 res1, FunKi _ arg2 res2)
         -> go arg1 arg2
            && go res1 res2

       _ -> False

{- *********************************************************************
*                                                                      *
            Kind LTEQ comparison
*                                                                      *
********************************************************************* -}

-- Returns 'False' when the kinds are not comparable.

tcLTEQMonoKind :: (HasDebugCallStack, IsVar kv) => MonoKind kv -> MonoKind kv -> Bool
tcLTEQMonoKind = lteqMonoKind

lteqMonoKind :: (HasCallStack, IsVar kv) => MonoKind kv -> MonoKind kv -> Bool
lteqMonoKind ka kb = lteq_mono_kind ka kb

lteq_mono_kind :: IsVar kv => MonoKind kv -> MonoKind kv -> Bool
lteq_mono_kind = inline_generic_lteq_mono_kind_x

{-# INLINE inline_generic_lteq_mono_kind_x #-}
inline_generic_lteq_mono_kind_x
  :: (VarHasUnique kv, Eq kv)
  => (MonoKind kv) -> (MonoKind kv) -> Bool
inline_generic_lteq_mono_kind_x = \k1 k2 -> k1 `seq` k2 `seq`
 case (k1, k2) of
   (BIKi k1, BIKi k2) -> k1 < k2

   (BIKi UKd, KiVarKi {}) -> True
   (KiVarKi {}, BIKi LKd) -> True

   _ -> False

