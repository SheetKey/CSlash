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

tcEqKind :: HasDebugCallStack => Kind kv -> Kind kv -> Bool
tcEqKind = eqKind

tcEqMonoKind :: HasDebugCallStack => MonoKind kv -> MonoKind kv -> Bool
tcEqMonoKind = eqMonoKind

initRnEnv :: Kind kv -> Kind kv -> RnEnv2 kv
initRnEnv ka kb = mkRnEnv2 $ mkInScopeSet $
                  kiVarsOfKind ka `unionVarSet` kiVarsOfKind kb

eqKind :: HasCallStack => Kind kv -> Kind kv -> Bool
eqKind ka kb = eq_kind ka kb

eqMonoKind :: HasCallStack => MonoKind kv -> MonoKind kv -> Bool
eqMonoKind ka kb = eq_mono_kind ka kb

eq_kind :: Kind kv -> Kind kv -> Bool
eq_kind = inline_generic_eq_kind_x Nothing

eq_mono_kind :: MonoKind kv -> MonoKind kv -> Bool
eq_mono_kind = inline_generic_eq_mono_kind_x Nothing

{-# NOINLINE generic_eq_kind_x #-}
generic_eq_kind_x :: Maybe (RnEnv2 kv) -> Kind kv -> Kind kv -> Bool
generic_eq_kind_x = inline_generic_eq_kind_x

{-# INLINE inline_generic_eq_kind_x #-}
inline_generic_eq_kind_x :: Maybe (RnEnv2 kv) -> (Kind kv) -> (Kind kv) -> Bool
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
generic_eq_mono_kind_x :: Maybe (RnEnv2 kv) -> (MonoKind kv) -> (MonoKind kv) -> Bool
generic_eq_mono_kind_x = inline_generic_eq_mono_kind_x

{-# INLINE inline_generic_eq_mono_kind_x #-}
inline_generic_eq_mono_kind_x :: Maybe (RnEnv2 kv) -> (MonoKind kv) -> (MonoKind kv) -> Bool
inline_generic_eq_mono_kind_x mb_env = \k1 k2 -> k1 `seq` k2 `seq`
  let go = generic_eq_mono_kind_x mb_env

      gos [] [] = True
      gos (k1:ks1) (k2:ks2) = go k1 k2 && gos ks1 ks2
      gos _ _ = False

  in case (k1, k2) of
       _ | 1# <- reallyUnsafePtrEquality# k1 k2 -> True

       (KiConApp kc1 kis1, KiConApp kc2 kis2)
         | kc1 == kc2
           -> gos kis1 kis2
         | otherwise
           -> False
           
       (KiVarKi kv1, KiVarKi kv2)
         -> case mb_env of
              Nothing -> kv1 == kv2
              Just env -> rnOccL env kv1 == rnOccR env kv2

       (FunKi _ arg1 res1, FunKi _ arg2 res2)
         -> go arg1 arg2
            && go res1 res2

       _ -> False
