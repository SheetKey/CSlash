{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Core.Type.Rep where

import {-# SOURCE #-} CSlash.Core.Type.Ppr (pprType)

import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Core.TyCon
import CSlash.Core.Kind

import CSlash.Builtin.Names

import CSlash.Types.Basic (LeftOrRight(..), pickLR)
import CSlash.Utils.Outputable
import CSlash.Data.FastString
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Binary
import CSlash.Utils.FV

import qualified Data.Data as Data hiding (TyCon)
import Control.DeepSeq

{- **********************************************************************
*                                                                       *
                        Type
*                                                                       *
********************************************************************** -}

data Type tv kv
  = TyVarTy tv
  | AppTy (Type tv kv) (Type tv kv) -- The first arg must be an 'AppTy' or a 'TyVarTy' or a 'TyLam'
  | TyLamTy tv (Type tv kv)
  | BigTyLamTy kv (Type tv kv)
  | TyConApp (TyCon tv kv) [Type tv kv]
  | ForAllTy {-# UNPACK #-} !(ForAllBinder tv) (Type tv kv)
  | FunTy
    { ft_kind :: MonoKind kv
    , ft_arg :: Type tv kv
    , ft_res :: Type tv kv
    }
  | CastTy (Type tv kv) (KindCoercion kv)
  | Embed (MonoKind kv) -- for application to a 'BigTyLamTy
  | KindCoercion (KindCoercion kv) -- embed a kind coercion (evidence stuff)
  deriving Data.Data

instance IsTyVar tv kv => Outputable (Type tv kv) where
  ppr = pprType

instance AsGenericTy Type where
  asGenericTyKi (TyVarTy tv) = TyVarTy $ toGenericTyVar $ asGenericKi tv
  asGenericTyKi (AppTy t1 t2) = AppTy (asGenericTyKi t1) (asGenericTyKi t2)
  asGenericTyKi (TyLamTy tv ty) = TyLamTy (toGenericTyVar $ asGenericKi tv) (asGenericTyKi ty)
  asGenericTyKi (BigTyLamTy kv ty) = BigTyLamTy (toGenericKiVar kv) (asGenericTyKi ty)
  asGenericTyKi (TyConApp tc tys) = TyConApp (asGenericTyKi tc) (asGenericTyKi <$> tys)
  asGenericTyKi (ForAllTy (Bndr tv af) ty)
    = ForAllTy (Bndr (toGenericTyVar $ asGenericKi tv) af) (asGenericTyKi ty)
  asGenericTyKi (FunTy k a r) = FunTy (asGenericKi k) (asGenericTyKi a) (asGenericTyKi r)
  asGenericTyKi (CastTy ty co) = CastTy (asGenericTyKi ty) (asGenericKi co)
  asGenericTyKi (Embed ki) = Embed (asGenericKi ki)
  asGenericTyKi (KindCoercion co) = KindCoercion (asGenericKi co)

instance AsAnyTy Type where
  asAnyTy (TyVarTy tv) = TyVarTy (toAnyTyVar tv)
  asAnyTy (AppTy t1 t2) = AppTy (asAnyTy t1) (asAnyTy t2)
  asAnyTy (TyLamTy tv ty) = TyLamTy (toAnyTyVar tv) (asAnyTy ty)
  asAnyTy (BigTyLamTy kv ty) = BigTyLamTy kv (asAnyTy ty)
  asAnyTy (TyConApp tc tys) = TyConApp (asAnyTy tc) (asAnyTy <$> tys)
  asAnyTy (ForAllTy (Bndr tv af) ty) = ForAllTy (Bndr (toAnyTyVar tv) af) (asAnyTy ty)
  asAnyTy (FunTy k a r) = FunTy k (asAnyTy a) (asAnyTy r)
  asAnyTy (CastTy ty co) = CastTy (asAnyTy ty) co
  asAnyTy (Embed ki) = Embed ki
  asAnyTy (KindCoercion co) = KindCoercion co

  asAnyTyKi (TyVarTy tv) = TyVarTy (asAnyKi $ toAnyTyVar tv)
  asAnyTyKi (AppTy t1 t2) = AppTy (asAnyTyKi t1) (asAnyTyKi t2)
  asAnyTyKi (TyLamTy tv ty) = TyLamTy (asAnyKi $ toAnyTyVar tv) (asAnyTyKi ty)
  asAnyTyKi (BigTyLamTy kv ty) = BigTyLamTy (toAnyKiVar kv) (asAnyTyKi ty)
  asAnyTyKi (TyConApp tc tys) = TyConApp (asAnyTyKi tc) (asAnyTyKi <$> tys)
  asAnyTyKi (ForAllTy (Bndr tv af) ty)
    = ForAllTy (Bndr (asAnyKi $ toAnyTyVar tv) af) (asAnyTyKi ty)
  asAnyTyKi (FunTy k a r) = FunTy (asAnyKi k) (asAnyTyKi a) (asAnyTyKi r)
  asAnyTyKi (CastTy ty co) = CastTy (asAnyTyKi ty) (asAnyKi co)
  asAnyTyKi (Embed ki) = Embed (asAnyKi ki)
  asAnyTyKi (KindCoercion co) = KindCoercion (asAnyKi co)

type KnotTied ty = ty

{- **********************************************************************
*                                                                       *
            Type FV instance
*                                                                       *
********************************************************************** -}

instance (Uniquable tv, Uniquable kv) => HasFVs (Type tv kv) where
  type FVInScope (Type tv kv) = (MkVarSet tv, MkVarSet kv)
  type FVAcc (Type tv kv) = ([tv], MkVarSet tv, [kv], MkVarSet kv)
  type FVArg (Type tv kv) = Either tv kv

  fvElemAcc (Left tv) (_, haveSet, _, _) = tv `elemVarSet` haveSet
  fvElemAcc (Right kv) (_, _, _, haveSet) = kv `elemVarSet` haveSet

  fvElemIS (Left tv) (in_scope, _) = tv `elemVarSet` in_scope
  fvElemIS (Right kv) (_, in_scope) = kv `elemVarSet` in_scope

  fvExtendAcc (Left tv) (have, haveSet, ks, kset) = (tv:have, extendVarSet haveSet tv, ks, kset)
  fvExtendAcc (Right kv) (ts, tset, have, haveSet) = (ts, tset, kv:have, extendVarSet haveSet kv)

  fvExtendIS (Left tv) (in_scope, ks) = (extendVarSet in_scope tv, ks)
  fvExtendIS (Right kv) (ts, in_scope) = (ts, extendVarSet in_scope kv)

  fvEmptyAcc = ([], emptyVarSet, [], emptyVarSet)
  fvEmptyIS = (emptyVarSet, emptyVarSet)

{- **********************************************************************
*                                                                       *
            Simple constructors
*                                                                       *
********************************************************************** -}

mkTyVarTy :: tv -> Type tv kv
mkTyVarTy v = TyVarTy v

mkTyVarTys :: [tv] -> [Type tv kv]
mkTyVarTys = map mkTyVarTy

mkNakedTyConTy :: TyCon tv kv -> Type tv kv
mkNakedTyConTy tycon = TyConApp tycon []

mkForAllTys :: [ForAllBinder tv] -> Type tv kv -> Type tv kv
mkForAllTys tyvars ty = foldr ForAllTy ty tyvars

tcMkFunTy :: MonoKind kv -> Type tv kv -> Type tv kv -> Type tv kv
tcMkFunTy = FunTy 

mkTyLamTy :: tv -> Type tv kv -> Type tv kv
mkTyLamTy = TyLamTy

mkTyLamTys :: [tv] -> Type tv kv -> Type tv kv
mkTyLamTys = flip (foldr mkTyLamTy)

mkBigLamTy :: kv -> Type tv kv -> Type tv kv
mkBigLamTy = BigTyLamTy

mkBigLamTys :: [kv] -> Type tv kv -> Type tv kv
mkBigLamTys = flip (foldr mkBigLamTy)

{- *********************************************************************
*                                                                      *
                foldType
*                                                                      *
********************************************************************* -}

data TypeFolder tv kv env env' b a  = TypeFolder
  { tf_view :: Type tv kv -> Maybe (Type tv kv)
  , tf_tyvar :: env -> tv -> a
  , tf_tybinder :: env -> tv -> ForAllFlag -> env
  , tf_tylambinder :: env -> tv -> env
  , tf_tylamkibinder :: env -> kv -> env
  , tf_swapEnv :: env -> env'
  , tf_embedKiRes :: b -> a
  , tf_mkcf :: MKiCoFolder kv env' b
  }

{-# INLINE foldType #-}
foldType
  :: (Monoid a, Monoid b, Outputable tv, Outputable kv, VarHasKind tv kv)
  => TypeFolder tv kv env env' b a
  -> env
  -> (Type tv kv -> a, [Type tv kv] -> a)
foldType (TypeFolder { tf_view = view
                     , tf_tyvar = tyvar
                     , tf_tybinder = tybinder
                     , tf_tylambinder = tylambinder
                     , tf_tylamkibinder = tylamkibinder
                     , tf_swapEnv = tokenv
                     , tf_embedKiRes = embedRes
                     , tf_mkcf = mkcf }) env
  = (go_ty env, go_tys env)
  where
    go_ty env ty | Just ty' <- view ty = go_ty env ty'
    go_ty env (TyVarTy tv) = tyvar env tv
    go_ty env (AppTy t1 t2) = go_ty env t1 `mappend` go_ty env t2
    go_ty env (TyLamTy tv ty) 
      = let !env' = tylambinder env tv
        in go_ty env' ty
    go_ty env (BigTyLamTy kv ty)
      = let !env' = tylamkibinder env kv
        in go_ty env' ty
    go_ty env (FunTy mki arg res) = embedRes (go_mki mki)
                                    `mappend` go_ty env arg
                                    `mappend` go_ty env res
      where go_mki = case foldMonoKiCo mkcf (tokenv env) of
                       (f, _, _, _) -> f
    go_ty env (TyConApp _ tys) = go_tys env tys
    go_ty env (ForAllTy (Bndr tv vis) inner)
      = let !env' = tybinder env tv vis
        in embedRes (go_mki (varKind tv)) `mappend` go_ty env' inner
      where go_mki = case foldMonoKiCo mkcf (tokenv env) of
                       (f, _, _, _) -> f
    go_ty env (Embed mki) = embedRes $ go_mki mki
      where go_mki = case foldMonoKiCo mkcf (tokenv env) of
                       (f, _, _, _) -> f
    go_ty env (CastTy ty kco) = go_ty env ty `mappend` embedRes (go_kco kco)
      where go_kco = case foldMonoKiCo mkcf (tokenv env) of
                       (_, _, f, _) -> f
    go_ty env (KindCoercion kco) = embedRes $ go_kco kco
      where go_kco = case foldMonoKiCo mkcf (tokenv env) of
                       (_, _, f, _) -> f

    go_tys _ [] = mempty
    go_tys env (t:ts) = go_ty env t `mappend` go_tys env ts

noView :: Type tv kv -> Maybe (Type tv kv)
noView _ = Nothing

{- *********************************************************************
*                                                                      *
                   typeSize
*                                                                      *
********************************************************************* -}

typeSize :: (IsTyVar tv kv, Outputable tv, Outputable kv) => Type tv kv -> Int
typeSize (TyVarTy {}) = 1
typeSize (AppTy t1 t2) = typeSize t1 + typeSize t2
typeSize (TyLamTy _ t) = 1 + typeSize t
typeSize (BigTyLamTy _ t) = 1 + typeSize t
typeSize (TyConApp _ ts) = 1 + typesSize ts
typeSize (ForAllTy (Bndr tv _) t) = panic "kindSize (varKind tv) + typeSize t"
typeSize (FunTy _ t1 t2) = typeSize t1 + typeSize t2
typeSize (Embed _) = 1
typeSize (CastTy ty _) = typeSize ty
typeSize co@(KindCoercion _) = pprPanic "typeSize" (ppr co)

typesSize :: (IsTyVar tv kv, Outputable tv, Outputable kv) => [Type tv kv] -> Int
typesSize tys = foldr ((+) . typeSize) 0 tys
