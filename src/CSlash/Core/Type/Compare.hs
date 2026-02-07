{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MagicHash #-}

module CSlash.Core.Type.Compare where

import CSlash.Cs.Pass

import CSlash.Core.Type ( typeKind, coreView, tcSplitAppTyNoView_maybe, splitAppTyNoView_maybe )

import CSlash.Core.Type.Rep
import CSlash.Core.Type.FVs
import CSlash.Core.TyCon
import CSlash.Core.Kind
import CSlash.Core.Kind.Compare hiding (initRnEnv)

import CSlash.Types.Var
import CSlash.Types.Unique
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic

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

tcEqType :: (HasDebugCallStack, HasPass p pass) => Type p -> Type p -> Bool
tcEqType = eqType
 
initRnEnv :: HasPass p pass => Type p -> Type p -> RnEnv2 (TyVar p)
initRnEnv ta tb = mkRnEnv2 $ mkInScopeSet all_vs
  where
    (tvs1, cvs1, _) = varsOfType ta
    (tvs2, cvs2, _) = varsOfType tb
    all_vs = panic "tvs1 `unionVarSet` mapVarSet toGenericTyVar cvs1 `unionVarSet`"
             --tvs2 `unionVarSet` mapVarSet toGenericTyVar cvs2

eqType :: (HasCallStack, HasPass p pass) => Type p -> Type p -> Bool
eqType ta tb = fullEq eq_type_expand ta tb

data SynFlag = ExpandSynonyms | KeepSynonyms

eq_type_expand :: HasPass p pass => Type p -> Type p -> Bool
eq_type_expand = inline_generic_eq_type_x ExpandSynonyms Nothing

{-# RULES
"eqType1" generic_eq_type_x ExpandSynonyms Nothing
          = eq_type_expand
#-}

generic_eq_type_x
  :: HasPass p pass => SynFlag -> Maybe (RnEnv2 (TyVar p)) -> Type p -> Type p -> Bool
{-# NOINLINE generic_eq_type_x #-}
generic_eq_type_x = inline_generic_eq_type_x

inline_generic_eq_type_x
  :: HasPass p pass => SynFlag -> Maybe (RnEnv2 (TyVar p)) -> Type p -> Type p -> Bool
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
                Just env -> rnOccL env tv1 == rnOccR env tv2

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
                       && generic_eq_type_x syn_flag (Just (rnBndr2 env tv1 tv2)) body1 body2
                  | otherwise
                    -> False

         _ -> False

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
