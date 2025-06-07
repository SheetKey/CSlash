{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Core.Type.Rep where

import {-# SOURCE #-} CSlash.Core.Type.Ppr (pprType)

import CSlash.Types.Var
import CSlash.Core.TyCon
import CSlash.Core.Kind

import CSlash.Builtin.Names

import CSlash.Types.Basic (LeftOrRight(..), pickLR)
import CSlash.Utils.Outputable
import CSlash.Data.FastString
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Binary

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
  | CastTy (Type tv kv) (KindCoercion kv tv)
  | Embed (MonoKind kv) -- for application to a 'BigTyLamTy
  | KindCoercion (KindCoercion kv tv) -- embed a kind coercion (evidence stuff)
  deriving Data.Data

instance (Outputable tv, Outputable kv) => Outputable (Type tv kv) where
  ppr = pprType

type KnotTied ty = ty

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

mkBigLamTys  :: [kv] -> Type tv kv -> Type tv kv
mkBigLamTys = flip (foldr mkBigLamTy)

{- *********************************************************************
*                                                                      *
                foldType
*                                                                      *
********************************************************************* -}

data TypeFolder tv kv env a = TypeFolder
  { tf_view :: Type tv kv -> Maybe (Type tv kv)
  , tf_tyvar :: env -> tv -> a
  , tf_tybinder :: env -> tv -> ForAllFlag -> env
  , tf_tylambinder :: env -> tv -> env
  , tf_tylamkibinder :: env -> kv -> env
  , tf_embed_mono_ki :: env -> MonoKind kv -> a
  }

-- Unlike GHC, we do not deal with kind variables here.
-- I.e., they are not added to the env.
{-# INLINE foldType #-}
foldType
  :: (Monoid a, Outputable tv, Outputable kv)
  => TypeFolder tv kv env a
  -> env
  -> (Type tv kv -> a, [Type tv kv] -> a)
foldType (TypeFolder { tf_view = view
                     , tf_tyvar = tyvar
                     , tf_tybinder = tybinder
                     , tf_tylambinder = tylambinder
                     , tf_tylamkibinder = tylamkibinder }) env
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
    go_ty env (FunTy _ arg res) = go_ty env arg `mappend` go_ty env res
    go_ty env (TyConApp _ tys) = go_tys env tys
    go_ty env (ForAllTy (Bndr tv vis) inner)
      = let !env' = tybinder env tv vis
        in go_ty env' inner
    go_ty _ (Embed _) = mempty
    go_ty env (CastTy ty _) = go_ty env ty
    go_ty _ co@(KindCoercion {}) = pprPanic "foldType" (ppr co)

    go_tys _ [] = mempty
    go_tys env (t:ts) = go_ty env t `mappend` go_tys env ts

noView :: Type tv kv -> Maybe (Type tv kv)
noView _ = Nothing

{- *********************************************************************
*                                                                      *
                   typeSize
*                                                                      *
********************************************************************* -}

typeSize :: (VarHasKind tv kv, Outputable tv, Outputable kv) => Type tv kv -> Int
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

typesSize :: (VarHasKind tv kv, Outputable tv, Outputable kv) => [Type tv kv] -> Int
typesSize tys = foldr ((+) . typeSize) 0 tys
