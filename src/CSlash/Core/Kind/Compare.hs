{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}

module CSlash.Core.Kind.Compare where

import CSlash.Core.Kind
import CSlash.Core.Kind.FVs

import {-# SOURCE #-} CSlash.Types.Var.KiVar
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

tcEqKind :: (HasDebugCallStack) => Kind p -> Kind p -> Bool
tcEqKind = eqKind

tcEqMonoKind :: (HasDebugCallStack) => MonoKind p -> MonoKind p -> Bool
tcEqMonoKind = eqMonoKind

initRnEnv :: Kind p -> Kind p -> RnEnv2 (KiVar p)
initRnEnv ka kb = mkRnEnv2 $ mkInScopeSet $
                  varsOfKind ka `unionVarSet` varsOfKind kb

eqKind :: (HasCallStack) => Kind p -> Kind p -> Bool
eqKind ka kb = eq_kind ka kb

eqMonoKind :: (HasCallStack) => MonoKind p -> MonoKind p -> Bool
eqMonoKind ka kb = eq_mono_kind ka kb

eq_kind :: Kind p -> Kind p -> Bool
eq_kind = inline_generic_eq_kind_x Nothing

eq_mono_kind :: MonoKind p -> MonoKind p -> Bool
eq_mono_kind = inline_generic_eq_mono_kind_x Nothing

{-# NOINLINE generic_eq_kind_x #-}
generic_eq_kind_x :: Maybe (RnEnv2 (KiVar p)) -> Kind p -> Kind p -> Bool
generic_eq_kind_x = inline_generic_eq_kind_x

{-# INLINE inline_generic_eq_kind_x #-}
inline_generic_eq_kind_x
  :: Maybe (RnEnv2 (KiVar p)) -> Kind p -> Kind p -> Bool
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
  :: Maybe (RnEnv2 (KiVar p)) -> (MonoKind p) -> (MonoKind p) -> Bool
generic_eq_mono_kind_x = inline_generic_eq_mono_kind_x

{-# INLINE inline_generic_eq_mono_kind_x #-}
inline_generic_eq_mono_kind_x
  :: Maybe (RnEnv2 (KiVar p)) -> MonoKind p -> MonoKind p -> Bool
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

tcLTEQMonoKind :: (HasDebugCallStack) => MonoKind p -> MonoKind p -> Bool
tcLTEQMonoKind = lteqMonoKind

lteqMonoKind :: (HasCallStack) => MonoKind p -> MonoKind p -> Bool
lteqMonoKind ka kb = lteq_mono_kind ka kb

lteq_mono_kind :: MonoKind p -> MonoKind p -> Bool
lteq_mono_kind = inline_generic_lteq_mono_kind_x

{-# INLINE inline_generic_lteq_mono_kind_x #-}
inline_generic_lteq_mono_kind_x
  :: MonoKind p -> MonoKind p -> Bool
inline_generic_lteq_mono_kind_x = \k1 k2 -> k1 `seq` k2 `seq`
 case (k1, k2) of
   (BIKi k1, BIKi k2) -> k1 < k2

   (BIKi UKd, KiVarKi {}) -> True
   (KiVarKi {}, BIKi LKd) -> True

   _ -> False

