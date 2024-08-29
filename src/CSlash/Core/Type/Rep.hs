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
  | AppTy Type Type -- The first arg must be an 'AppTy' or a 'TyVarTy'.
  | TyConApp TyCon [Type]
  | ForAllTy {-# UNPACK #-} !ForAllTyBinder Type
  | FunTy
    { ft_kind :: Kind
    , ft_arg :: Type
    , ft_res :: Type
    }
  | WithContext Kind Type -- this should occure at most once per type and always as the first cons
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
mkTyVarTy v = assertPpr (isTyVar v) (ppr v <+> colon <+> ppr (varKind v)) $
              TyVarTy v

mkTyVarTys :: [TypeVar] -> [Type]
mkTyVarTys = map mkTyVarTy

mkNakedTyConTy :: TyCon -> Type
mkNakedTyConTy tycon = TyConApp tycon []

{- *********************************************************************
*                                                                      *
                foldType
*                                                                      *
********************************************************************* -}

data TypeFolder env a = TypeFolder
  { tf_view :: Type -> Maybe Type
  , tf_tyvar :: env -> TypeVar -> a
  , tf_tybinder :: env -> TypeVar -> ForAllTyFlag -> env
  }

-- Unlike GHC, we do not deal with kind variables here.
-- I.e., they are not added to the env.
{-# INLINE foldType #-}
foldType :: Monoid a => TypeFolder env a -> env -> (Type -> a, [Type] -> a)
foldType (TypeFolder { tf_view = view
                     , tf_tyvar = tyvar
                     , tf_tybinder = tybinder }) env
  = (go_ty env, go_tys env)
  where
    go_ty env ty | Just ty' <- view ty = go_ty env ty'
    go_ty env (TyVarTy tv) = tyvar env tv
    go_ty env (AppTy t1 t2) = go_ty env t1 `mappend` go_ty env t2
    go_ty env (FunTy _ arg res) = go_ty env arg `mappend` go_ty env res
    go_ty env (ForAllTy (Bndr tv vis) inner)
      = let !env' = tybinder env tv vis
        in go_ty env' inner

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
typeSize (TyConApp _ ts) = 1 + typesSize ts
typeSize (ForAllTy (Bndr tv _) t) = typeSize (varType tv) + typeSize t
typeSize (FunTy _ t1 t2) = typeSize t1 + typeSize t2

typesSize :: [Type] -> Int
typesSize tys = foldr ((+) . typeSize) 0 tys
