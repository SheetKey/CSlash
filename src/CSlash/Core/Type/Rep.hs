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

data Type
  = TyVarTy Var
  | AppTy Type Type -- The first arg must be an 'AppTy' or a 'TyVarTy' or a 'TyLam'
  | TyLamTy TypeVar Type
  | BigTyLamTy KindVar Type
  | TyConApp TyCon [Type]
  | ForAllTy {-# UNPACK #-} !ForAllTyBinder Type
  | FunTy
    { ft_kind :: MonoKind
    , ft_arg :: Type
    , ft_res :: Type
    }
  | Embed MonoKind -- for application to a 'BigTyLamTy
  | CastTy Type KindCoercion
  deriving Data.Data

instance Outputable Type where
  ppr = pprType

type KnotTied ty = ty

{- **********************************************************************
*                                                                       *
            Simple constructors
*                                                                       *
********************************************************************** -}

mkTyVarTy :: TypeVar -> Type
mkTyVarTy v = assertPpr (isTyVar v) (ppr v <+> colon <+> ppr (varKindMaybe v)) $
              TyVarTy v

mkTyVarTys :: [TypeVar] -> [Type]
mkTyVarTys = map mkTyVarTy

mkNakedTyConTy :: TyCon -> Type
mkNakedTyConTy tycon = TyConApp tycon []

mkForAllTys :: [ForAllTyBinder] -> Type -> Type
mkForAllTys tyvars ty = foldr ForAllTy ty tyvars

tcMkFunTy :: MonoKind -> Type -> Type -> Type
tcMkFunTy = FunTy 

mkTyLamTy :: TypeVar -> Type -> Type
mkTyLamTy = TyLamTy

mkTyLamTys :: [TypeVar] -> Type -> Type
mkTyLamTys = flip (foldr mkTyLamTy)

mkBigLamTy :: KindVar -> Type -> Type
mkBigLamTy = BigTyLamTy

mkBigLamTys  :: [KindVar] -> Type -> Type
mkBigLamTys = flip (foldr mkBigLamTy)

{- *********************************************************************
*                                                                      *
                foldType
*                                                                      *
********************************************************************* -}

data TypeFolder env a = TypeFolder
  { tf_view :: Type -> Maybe Type
  , tf_tyvar :: env -> TypeVar -> a
  , tf_tybinder :: env -> TypeVar -> ForAllTyFlag -> env
  , tf_tylambinder :: env -> TypeVar -> env
  , tf_tylamkibinder :: env -> KindVar -> env
  , tf_embed_mono_ki :: env -> MonoKind -> a
  }

-- Unlike GHC, we do not deal with kind variables here.
-- I.e., they are not added to the env.
{-# INLINE foldType #-}
foldType :: Monoid a => TypeFolder env a -> env -> (Type -> a, [Type] -> a)
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

    go_tys _ [] = mempty
    go_tys env (t:ts) = go_ty env t `mappend` go_tys env ts

noView :: Type -> Maybe Type
noView _ = Nothing

{- *********************************************************************
*                                                                      *
                   typeSize
*                                                                      *
********************************************************************* -}

typeSize :: Type -> Int
typeSize (TyVarTy {}) = 1
typeSize (AppTy t1 t2) = typeSize t1 + typeSize t2
typeSize (TyLamTy _ t) = 1 + typeSize t
typeSize (BigTyLamTy _ t) = 1 + typeSize t
typeSize (TyConApp _ ts) = 1 + typesSize ts
typeSize (ForAllTy (Bndr tv _) t) = typeSize (varType tv) + typeSize t
typeSize (FunTy _ t1 t2) = typeSize t1 + typeSize t2
typeSize (Embed _) = 1
typeSize (CastTy ty _) = typeSize ty

typesSize :: [Type] -> Int
typesSize tys = foldr ((+) . typeSize) 0 tys
