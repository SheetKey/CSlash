module CSlash.Core.Type
  ( Type(..), ForAllTyFlag(..) -- , FunTyFlag(..)
  , Var, TypeVar, isTyVar, ForAllTyBinder
  , KnotTied

  , mkTyVarTy, mkTyVarTys

  , mkAppTy, mkAppTys

  , mkTyConApp, mkTyConTy

  , binderVar, binderVars

  , coreView
  ) where

import CSlash.Types.Basic

import CSlash.Core.Type.Rep
import CSlash.Core.Type.Subst
import CSlash.Core.Type.FVs

import CSlash.Core.Kind.Subst

import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Unique.Set

import CSlash.Core.TyCon
import CSlash.Builtin.Types.Prim

-- import {-# SOURCE #-} CSlash.Builtin.Types
--    ( charTy, naturalTy
--    , typeSymbolKind, liftedTypeKind, unliftedTypeKind
--    , constraintKind, zeroBitTypeKind
--    , manyDataConTy, oneDataConTy
--    , liftedRepTy, unliftedRepTy, zeroBitRepTy )

import CSlash.Types.Name( Name )
import CSlash.Builtin.Names

-- import {-# SOURCE #-} CSlash.Tc.Utils.TcType ( isConcreteTyVar )

import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Data.FastString

import CSlash.Data.Maybe ( orElse, isJust, firstJust )

{- *********************************************************************
*                                                                      *
                Type representation
*                                                                      *
********************************************************************* -}

coreView :: Type -> Maybe Type
coreView (TyConApp tc tys) = expandSynTyConApp_maybe tc tys
coreView _ = Nothing
{-# INLINE coreView #-}

expandSynTyConApp_maybe :: TyCon -> [Type] -> Maybe Type
expandSynTyConApp_maybe tc arg_tys
  | Just (tvs, rhs) <- synTyConDefn_maybe tc
  , arg_tys `saturates` tyConArity tc
  = Just $! (expand_syn tvs rhs arg_tys)
  | otherwise
  = Nothing

saturates :: [Type] -> Arity -> Bool
saturates _ 0 = True
saturates [] _ = False
saturates (_:tys) n = assert (n >= 0) $ saturates tys (n-1)

expand_syn :: [TypeVar] -> Type -> [Type] -> Type
expand_syn tvs rhs arg_tys
  | null arg_tys = assert (null tvs) rhs
  | null tvs = mkAppTys rhs arg_tys
  | otherwise = go empty_subst tvs arg_tys
  where
    empty_subst = mkEmptySubst in_scope
    in_scope = mkInScopeSet $ shallowTyVarsOfTypes $ arg_tys

    go subst [] tys
      | null tys = rhs'
      | otherwise = mkAppTys rhs' tys
      where
        rhs' = substTy subst rhs
    go subst (tv:tvs) (ty:tys) = go (extendTvSubst subst tv ty) tvs tys
    go _ (_:_) [] = pprPanic "expand_syn" (ppr tvs $$ ppr rhs $$ ppr arg_tys)

{- *********************************************************************
*                                                                      *
                      AppTy
*                                                                      *
********************************************************************* -}

mkAppTy :: Type -> Type -> Type
mkAppTy (TyConApp tc tys) ty2 = mkTyConApp tc (tys ++ [ty2])
mkAppTy ty1 ty2 = AppTy ty1 ty2

mkAppTys :: Type -> [Type] -> Type
mkAppTys ty1 [] = ty1
mkAppTys (TyConApp tc tys1) tys2 = mkTyConApp tc (tys1 ++ tys2)
mkAppTys ty1 tys2 = foldl' AppTy ty1 tys2

{- *********************************************************************
*                                                                      *
                    Space-saving construction
*                                                                      *
********************************************************************* -}

mkTyConApp :: TyCon -> [Type] -> Type
mkTyConApp tycon [] = mkTyConTy tycon
mkTyConApp tycon tys = TyConApp tycon tys
