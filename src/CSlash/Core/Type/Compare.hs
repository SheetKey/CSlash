{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MagicHash #-}

module CSlash.Core.Type.Compare where

import CSlash.Cs.Pass

import CSlash.Core.Type
  ( typeKind, coreView, tcSplitAppTyNoView_maybe, splitAppTyNoView_maybe, tycoercionTypes )

import CSlash.Core.Type.FVs
import CSlash.Core.TyCon
import CSlash.Core.Kind

import CSlash.Types.Var
import CSlash.Types.Unique
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Data.Pair
import CSlash.Data.Maybe

import GHC.Base (reallyUnsafePtrEquality#)

import qualified Data.Semigroup as S

{- *********************************************************************
*                                                                      *
                       Type equality

     We don't use (==) from class Eq, partly so that we know where
     type equality is called, and partly because there are multiple
     variants.
*                                                                      *
********************************************************************* -}

type EqEnv p = (RnEnv2 (TyVar p), RnEnv2 (KiVar p))

tcEqType :: (HasDebugCallStack, HasPass p pass) => Type p -> Type p -> Bool
tcEqType = eqType
 
tcEqKind :: (HasDebugCallStack, HasPass p p') => Kind p -> Kind p -> Bool
tcEqKind = eqKind

tcEqMonoKind :: (HasDebugCallStack, HasPass p pass) => MonoKind p -> MonoKind p -> Bool
tcEqMonoKind = eqMonoKind

initKvRnEnv :: HasPass p p' => Kind p -> Kind p -> EqEnv p
initKvRnEnv ka kb =
  ( mkRnEnv2 $ emptyInScopeSet
  , mkRnEnv2 $ mkInScopeSet $ varsOfKind ka `unionVarSet` varsOfKind kb
  )

initRnEnv :: HasPass p pass => Type p -> Type p -> EqEnv p
initRnEnv ta tb =
  ( mkRnEnv2 $ mkInScopeSet $ tvs1 `unionVarSet` tvs2
  , mkRnEnv2 $ mkInScopeSet $ kvs1 `unionVarSet` kvs2
  )
  where
    (tvs1, cvs1, kvs1) = varsOfType ta
    (tvs2, cvs2, kvs2) = varsOfType tb

eqType :: (HasCallStack, HasPass p pass) => Type p -> Type p -> Bool
eqType ta tb = fullEq eq_type_expand ta tb

eqKind :: (HasCallStack, HasPass p p') => Kind p -> Kind p -> Bool
eqKind ka kb = eq_kind ka kb

eqMonoKind :: (HasCallStack, HasPass p pass) => MonoKind p -> MonoKind p -> Bool
eqMonoKind ka kb = eq_mono_kind ka kb

data SynFlag = ExpandSynonyms | KeepSynonyms

eq_type_expand :: HasPass p pass => Type p -> Type p -> Bool
eq_type_expand = inline_generic_eq_type_x ExpandSynonyms Nothing

eq_kind :: HasPass p p' => Kind p -> Kind p -> Bool
eq_kind = inline_generic_eq_kind_x Nothing

eq_mono_kind :: HasPass p pass => MonoKind p -> MonoKind p -> Bool
eq_mono_kind = inline_generic_eq_mono_kind_x Nothing

{-# RULES
"eqType1" generic_eq_type_x ExpandSynonyms Nothing
          = eq_type_expand
#-}

generic_eq_type_x
  :: HasPass p pass => SynFlag -> Maybe (EqEnv p) -> Type p -> Type p -> Bool
{-# NOINLINE generic_eq_type_x #-}
generic_eq_type_x = inline_generic_eq_type_x

{-# NOINLINE generic_eq_kind_x #-}
generic_eq_kind_x :: HasPass p p' => Maybe (EqEnv p) -> Kind p -> Kind p -> Bool
generic_eq_kind_x = inline_generic_eq_kind_x

inline_generic_eq_type_x
  :: HasPass p pass => SynFlag -> Maybe (EqEnv p) -> Type p -> Type p -> Bool
{-# INLINE inline_generic_eq_type_x #-}
inline_generic_eq_type_x syn_flag mb_env
  = \t1 t2 -> t1 `seq` t2 `seq`
    let go = generic_eq_type_x syn_flag mb_env

        gos [] [] = True
        gos (t1:ts1) (t2:ts2) = go t1 t2 && gos ts1 ts2
        gos _ _ = False

    in case (t1, t2) of
         _ | 1# <- reallyUnsafePtrEquality# t1 t2 -> True

         (TyConApp tc1 tys1, TyConApp tc2 tys2)
           | tc1 == tc2, not (isForgetfulSynTyCon tc1)
             -> gos tys1 tys2

         _ | ExpandSynonyms <- syn_flag, Just t1' <- coreView t1 -> go t1' t2
           | ExpandSynonyms <- syn_flag, Just t2' <- coreView t2 -> go t1 t2'

         (TyConApp tc1 ts1, TyConApp tc2 ts2)
           | tc1 == tc2 -> gos ts1 ts2
           | otherwise -> False

         (TyVarTy tv1, TyVarTy tv2)
           -> case mb_env of
                Nothing -> tv1 == tv2
                Just env -> rnTvOccL env tv1 == rnTvOccR env tv2

         (CastTy t1' _, _) -> go t1' t2
         (_, CastTy t2' _) -> go t1 t2'
         (KindCoercion {}, KindCoercion {}) -> True

         (FunTy _ arg1 res1, FunTy _ arg2 res2)
           -> fullEq go arg1 arg2
              && fullEq go res1 res2

         (AppTy s1 t1', _)
           | Just (s2, t2') <- tcSplitAppTyNoView_maybe t2
             -> go s1 s2 && go t1' t2'

         (_, AppTy s2 t2')
           | Just (s1, t1') <- tcSplitAppTyNoView_maybe t1
             -> go s1 s2 && go t1' t2'

         (ForAllTy (Bndr tv1 vis1) body1, ForAllTy (Bndr tv2 vis2) body2)
           -> case mb_env of
                Nothing -> generic_eq_type_x syn_flag (Just (initRnEnv t1 t2)) t1 t2
                Just env
                  | vis1 == vis2
                    -> eqMonoKind (varKind tv1) (varKind tv2)
                       && generic_eq_type_x syn_flag (Just (rnTvBndr2 env tv1 tv2)) body1 body2
                  | otherwise
                    -> False

         _ -> False

{-# INLINE inline_generic_eq_kind_x #-}
inline_generic_eq_kind_x
  :: HasPass p p' => Maybe (EqEnv p) -> Kind p -> Kind p -> Bool
inline_generic_eq_kind_x mb_env = \k1 k2 -> k1 `seq` k2 `seq`
  let go = generic_eq_kind_x mb_env
      go_mono = generic_eq_mono_kind_x mb_env
  in case (k1, k2) of
       (Mono k1, Mono k2) -> go_mono k1 k2
       (ForAllKi kv1 body1, ForAllKi kv2 body2)
         -> case mb_env of
              Nothing -> generic_eq_kind_x (Just (initKvRnEnv k1 k2)) k1 k2
              Just env -> generic_eq_kind_x (Just (rnKvBndr2 env kv1 kv2)) body1 body2
       _ -> False

{-# NOINLINE generic_eq_mono_kind_x #-}
generic_eq_mono_kind_x
  :: HasPass p pass => Maybe (EqEnv p) -> (MonoKind p) -> (MonoKind p) -> Bool
generic_eq_mono_kind_x = inline_generic_eq_mono_kind_x

{-# INLINE inline_generic_eq_mono_kind_x #-}
inline_generic_eq_mono_kind_x
  :: HasPass p pass => Maybe (EqEnv p) -> MonoKind p -> MonoKind p -> Bool
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
              Just env -> rnKvOccL env kv1 == rnKvOccR env kv2

       (FunKi _ arg1 res1, FunKi _ arg2 res2)
         -> go arg1 arg2
            && go res1 res2

       (KiConApp kc1, KiConApp kc2)
         | let (k1, env1) = flattenKiCon kc1
               (k2, env2) = flattenKiCon kc2
         , go k1 k2
           -> let (leftover1, leftover2, zipped) = zipRowSigEnvs env1 env2
              in if not (isEmptyRowEnv env1 && isEmptyRowEnv env2)
                 then False
                 else nonDetFoldRowEnv (\pair b -> b && eq_row_sig mb_env pair) True zipped

       _ -> False

eq_row_sig :: HasPass p pass => Maybe (EqEnv p) -> (RowSig p, RowSig p) -> Bool
eq_row_sig env (RowTySig _ t1, RowTySig _ t2) = generic_eq_type_x ExpandSynonyms env t1 t2
eq_row_sig env (RowKiSig _ k1, RowKiSig _ k2) = generic_eq_mono_kind_x env k1 k2
eq_row_sig env other = pprPanic "eq_row_sig mismatch" (ppr other)

fullEq
  :: HasPass p pass
  => (Type p -> Type p -> Bool)
  -> Type p -> Type p -> Bool
{-# INLINE fullEq #-}
fullEq eq ty1 ty2 = case eq ty1 ty2 of
                      False -> False
                      True | hasCasts ty1 || hasCasts ty2
                             -> eqKind (typeKind ty1) (typeKind ty2)
                           | otherwise
                             -> True

hasCasts :: Type p -> Bool
hasCasts (CastTy {}) = True
hasCasts (KindCoercion {}) = True
hasCasts (AppTy t1 t2) = hasCasts t1 || hasCasts t2
hasCasts (ForAllTy _ ty) = hasCasts ty
hasCasts _ = False

-- BELOW THIS LINE BELONGS ELSEWHERE

isReflexiveTyCo :: HasPass p pass => TypeCoercion p -> Bool
isReflexiveTyCo = isJust . isReflexiveTyCo_maybe

isReflexiveTyCo_maybe :: HasPass p pass => TypeCoercion p -> Maybe (Type p)
isReflexiveTyCo_maybe (TyRefl ty) = Just ty
isReflexiveTyCo_maybe (GRefl ty kco) | isReflKiCo kco = Just ty
isReflexiveTyCo_maybe co
  | ty1 `eqType` ty2
  = Just ty1
  | otherwise
  = Nothing
  where (Pair ty1 ty2) = tycoercionTypes co

{- *********************************************************************
*                                                                      *
              MCoercion
*                                                                      *
********************************************************************* -}

checkReflexiveMCo :: HasPass p pass => MTypeCoercion p -> MTypeCoercion p
checkReflexiveMCo MRefl = MRefl
checkReflexiveMCo (MCo co)
  | isReflexiveTyCo co = MRefl
  | otherwise = MCo co

{- *********************************************************************
*                                                                      *
            Kind LTEQ comparison
*                                                                      *
********************************************************************* -}

-- Returns 'False' when the kinds are not comparable.

tcLTEQMonoKind :: (HasDebugCallStack, HasPass p pass) => MonoKind p -> MonoKind p -> Bool
tcLTEQMonoKind = lteqMonoKind

lteqMonoKind :: (HasCallStack, HasPass p pass) => MonoKind p -> MonoKind p -> Bool
lteqMonoKind ka kb = lteq_mono_kind ka kb

lteq_mono_kind :: HasPass p pass => MonoKind p -> MonoKind p -> Bool
lteq_mono_kind = inline_generic_lteq_mono_kind_x

{-# INLINE inline_generic_lteq_mono_kind_x #-}
inline_generic_lteq_mono_kind_x
  :: HasPass p pass => MonoKind p -> MonoKind p -> Bool
inline_generic_lteq_mono_kind_x = \k1 k2 -> k1 `seq` k2 `seq`
 case (k1, k2) of
   (BIKi k1, BIKi k2) -> k1 < k2

   (BIKi UKd, KiVarKi {}) -> True
   (KiVarKi {}, BIKi LKd) -> True

   _ -> False

{- *********************************************************************
*                                                                      *
            Env utilies
*                                                                      *
********************************************************************* -}

rnTvOccL :: EqEnv p -> TyVar p -> TyVar p
rnTvOccL (env, _) tv = rnOccL env tv

rnKvOccL :: EqEnv p -> KiVar p -> KiVar p
rnKvOccL (_, env) kv = rnOccL env kv

rnTvOccR :: EqEnv p -> TyVar p -> TyVar p
rnTvOccR (env, _) tv = rnOccR env tv

rnKvOccR :: EqEnv p -> KiVar p -> KiVar p
rnKvOccR (_, env) kv = rnOccR env kv

rnTvBndr2 :: EqEnv p -> TyVar p -> TyVar p -> EqEnv p
rnTvBndr2 (env, kv_env) v1 v2 = (rnBndr2 env v1 v2, kv_env)

rnKvBndr2 :: EqEnv p -> KiVar p -> KiVar p -> EqEnv p
rnKvBndr2 (ty_env, env) v1 v2 = (ty_env, rnBndr2 env v1 v2)
