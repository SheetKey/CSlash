{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Type
  ( Type(..), ForAllTyFlag(..) -- , FunTyFlag(..)
  , Var, TypeVar, isTyVar, ForAllTyBinder
  , KnotTied

  , mkTyVarTy, mkTyVarTys

  , mkAppTy, mkAppTys

  , mkTyConTy

  , binderVar, binderVars

  , module CSlash.Core.Type
  ) where

import CSlash.Types.Basic

import CSlash.Core.Type.Rep
import CSlash.Core.Type.Subst
import CSlash.Core.Type.FVs

import CSlash.Core.Kind
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

coreFullView :: Type -> Type
coreFullView ty@(TyConApp tc _)
  | isTypeSynonymTyCon tc = core_full_view ty
coreFullView ty = ty
{-# INLINE coreFullView #-}

core_full_view :: Type -> Type
core_full_view ty
  | Just ty' <- coreView ty = core_full_view ty'
  | otherwise = ty

expandSynTyConApp_maybe :: TyCon -> [Type] -> Maybe Type
expandSynTyConApp_maybe tc arg_tys
  | Just rhs <- synTyConDefn_maybe tc
  , arg_tys `saturates` tyConArity tc
  = Just $! (expand_syn rhs arg_tys)
  | otherwise
  = Nothing

saturates :: [Type] -> Arity -> Bool
saturates _ 0 = True
saturates [] _ = False
saturates (_:tys) n = assert (n >= 0) $ saturates tys (n-1)

expand_syn :: Type -> [Type] -> Type
expand_syn rhs arg_tys
  | null arg_tys = rhs
  | otherwise = go rhs empty_subst arg_tys
  where
    empty_subst = mkEmptySubst in_scope
    in_scope = mkInScopeSet $ shallowTyVarsOfTypes $ arg_tys

    go (TyLamTy _ _) _ [] = pprPanic "expand_syn" (ppr rhs $$ ppr arg_tys)
    go ty subst [] = substTy subst ty
    go (TyLamTy tv ty) subst (arg:args) = go ty (extendTvSubst subst tv arg) args
    go ty subst args = mkAppTys (substTy subst ty) args

{- *********************************************************************
*                                                                      *
                      mapType
*                                                                      *
********************************************************************* -}

data TypeMapper env m = TypeMapper
  { tcm_tyvar :: env -> TypeVar -> m Type
  , tcm_tybinder :: forall r. env -> TypeVar -> ForAllTyFlag -> (env -> TypeVar -> m r) -> m r
  , tcm_tylambinder :: forall r. env -> TypeVar -> (env -> TypeVar -> m r) -> m r
  , tcm_tycon :: TyCon -> m TyCon
  }

{-# INLINE mapType #-}
mapType
  :: Monad m => TypeMapper () m
  -> ( Type -> m Type
     , [Type] -> m [Type] )
mapType mapper = case mapTypeX mapper of
                   (go_ty, go_tys) -> (go_ty (), go_tys ())

{-# INLINE mapTypeX #-}
mapTypeX
  :: Monad m => TypeMapper env m
  -> ( env -> Type -> m Type
     , env -> [Type] -> m [Type] )
mapTypeX (TypeMapper { tcm_tyvar = tyvar
                     , tcm_tybinder = tybinder
                     , tcm_tycon = tycon
                     , tcm_tylambinder = tylambinder })
  = (go_ty, go_tys)
  where
    go_tys !_ [] = return []
    go_tys !env (ty:tys) = (:) <$> go_ty env ty <*> go_tys env tys

    go_ty !env (TyVarTy tv) = tyvar env tv
    go_ty !env (AppTy t1 t2) = mkAppTy <$> go_ty env t1 <*> go_ty env t2
    go_ty !env ty@(FunTy _ arg res) = do
      arg' <- go_ty env arg
      res' <- go_ty env res
      return $ ty { ft_arg = arg', ft_res = res' }
    go_ty !env ty@(TyConApp tc tys)
      | isTcTyCon tc
      = do tc' <- tycon tc
           mkTyConApp tc' <$> go_tys env tys
      | null tys
      = return ty
      | otherwise
      = mkTyConApp tc <$> go_tys env tys
    go_ty !env (ForAllTy (Bndr tv vis) inner) = do
      tybinder env tv vis $ \env' tv' -> do
        inner' <- go_ty env' inner
        return $ ForAllTy (Bndr tv' vis) inner'
    go_ty !env (TyLamTy tv inner) = do
      tylambinder env tv $ \env' tv' -> do
        inner' <- go_ty env' inner
        return $ TyLamTy tv' inner'
    go_ty !env (WithContext ki ty) = WithContext ki <$> go_ty env ty

{- *********************************************************************
*                                                                      *
                      TyVarTy
*                                                                      *
********************************************************************* -}

getTyVar_maybe :: Type -> Maybe TypeVar
getTyVar_maybe = repGetTyVar_maybe . coreFullView

repGetTyVar_maybe :: Type -> Maybe TypeVar
repGetTyVar_maybe (TyVarTy tv) = Just tv
repGetTyVar_maybe _ = Nothing

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
                      LitTy
*                                                                      *
********************************************************************* -}

type ErrorMsgType = Type

{- *********************************************************************
*                                                                      *
                      FunTy
*                                                                      *
********************************************************************* -}

piResultTys :: HasDebugCallStack => Kind -> [Type] -> Kind
piResultTys ki [] = ki
piResultTys ki orig_args@(arg:args)
  | FunKd { kft_res = res } <- ki
  = piResultTys res args
  | otherwise
  = pprPanic "piResultTys1" (ppr ki $$ ppr orig_args)

{- *********************************************************************
*                                                                      *
        ForAllTy
*                                                                      *
********************************************************************* -}

splitForAllTyVars :: Type -> ([TypeVar], Type)
splitForAllTyVars ty = split ty ty []
  where
    split _ (ForAllTy (Bndr tv _) ty) tvs = split ty ty (tv:tvs)
    split orig_ty ty tvs | Just ty' <- coreView ty = split orig_ty ty' tvs
    split orig_ty _ tvs = (reverse tvs, orig_ty)

isTauTy :: Type -> Bool
isTauTy ty | Just ty' <- coreView ty = isTauTy ty'
isTauTy (TyVarTy _) = True
isTauTy (TyConApp tc tys) = all isTauTy tys && isTauTyCon tc
isTauTy (AppTy a b) = isTauTy a && isTauTy b
isTauTy (FunTy _ a b) = isTauTy a && isTauTy b
isTauTy (ForAllTy {}) = False
isTauTy (TyLamTy _ ty) = isTauTy ty
isTauTy other = pprPanic "isTauTy" (ppr other)

isForgetfulTy :: Type -> Bool
isForgetfulTy (TyVarTy _) = False
isForgetfulTy (TyConApp tc tys) = isForgetfulSynTyCon tc || any isForgetfulTy tys
isForgetfulTy (AppTy a b) = isForgetfulTy a || isForgetfulTy b
isForgetfulTy (FunTy _ a b) = isForgetfulTy a || isForgetfulTy b
isForgetfulTy (ForAllTy (Bndr tv _) ty)
  = (not $ tv `elemVarSet` tyVarsOfType ty) || isForgetfulTy ty
isForgetfulTy (TyLamTy tv ty) = (not $ tv `elemVarSet` tyVarsOfType ty) || isForgetfulTy ty
isForgetfulTy other = pprPanic "isForgetfulTy" (ppr other)

{- *********************************************************************
*                                                                      *
            Type families
*                                                                      *
********************************************************************* -}

{- NOTE:
We do note need the type to be KnotTied.
This is because we do not have recursive things the same way haskell does.
-}
buildSynTyCon :: Name -> [KindVar] -> Kind -> Kind -> Arity -> Type -> TyCon
buildSynTyCon name binders res_kind full_kind arity rhs
  = assertPpr (not $ uniqSetAny ((name ==) . tyConName) rhs_tycons)
    (vcat [ text "'buildSynTyCon' found a recursive tycon"
          , ppr name
          , ppr rhs ])
    mkSynonymTyCon name binders res_kind full_kind arity rhs is_tau is_forgetful is_concrete
  where
    is_tau = isTauTy rhs
    is_concrete = uniqSetAll isConcreteTyCon rhs_tycons
    is_forgetful = isForgetfulTy rhs

    rhs_tycons = tyConsOfType rhs

{- *********************************************************************
*                                                                      *
        The kind of a type
*                                                                      *
********************************************************************* -}

typeKind :: HasDebugCallStack => Type -> Kind
typeKind (TyConApp tc tys) = piResultTys (tyConKind tc) tys
typeKind (FunTy { ft_kind = kind }) = kind
typeKind (TyVarTy tyvar) = tyVarKind tyvar
typeKind (AppTy fun arg)
  = go fun [arg]
  where
    go (AppTy fun arg) args = go fun (arg:args)
    go fun args = piResultTys (typeKind fun) args
typeKind ty@(ForAllTy {})
  = let (tvs, body) = splitForAllTyVars ty
        body_kind = typeKind body
    in assertPpr (not (null tvs) && all isTyVar tvs) (ppr ty) body_kind
typeKind (TyLamTy tv res) = mkFunKi (tyVarKind tv) (typeKind res)
typeKind (WithContext ctxt ty) = mkContextKi ctxt (typeKind ty)       

{- *********************************************************************
*                                                                      *
                    Space-saving construction
*                                                                      *
********************************************************************* -}

mkTyConApp :: TyCon -> [Type] -> Type
mkTyConApp tycon [] = mkTyConTy tycon
mkTyConApp tycon tys = TyConApp tycon tys
