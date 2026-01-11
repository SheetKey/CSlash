{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Type
  ( Type(..), TypeCoercion(..), PredType, ForAllFlag(..) -- , FunTyFlag(..)
  , TyVar, AnyTyVar, AnyKiVar, TyCoVar, ForAllBinder
  , KnotTied

  , mkTyVarTy, mkTyVarTys

  , mkAppTy, mkAppTys

  , mkTyConTy

  , mkTyCoVarCo, mkTyHoleCo

  , mkBigLamTys

  , mkInvisForAllTys

  , isReflTyCo, mkSymTyCo

  , binderVar, binderVars

  , module CSlash.Core.Type
  ) where

import CSlash.Types.Basic

import CSlash.Core.Type.Rep
import CSlash.Core.Type.Subst
import CSlash.Core.Type.FVs

import CSlash.Core.Kind
import CSlash.Core.Kind.Compare
import CSlash.Core.Kind.FVs
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
import CSlash.Data.Pair

import CSlash.Data.Maybe ( orElse, isJust, firstJust, fromJust )
import Data.Bifunctor (bimap)
import Control.Monad ((>=>))

{- *********************************************************************
*                                                                      *
                Type representation
*                                                                      *
********************************************************************* -}

rewriterView :: IsTyVar tv kv => Type tv kv -> Maybe (Type tv kv)
rewriterView (TyConApp tc tys)
  | isTypeSynonymTyCon tc
  , isForgetfulSynTyCon tc
  = expandSynTyConApp_maybe tc tys
rewriterView ty@(AppTy{}) = expandTyLamApp_maybe ty (not . isForgetfulTy)
rewriterView _ = Nothing
{-# INLINE rewriterView #-}

coreView :: IsTyVar tv kv => Type tv kv -> Maybe (Type tv kv)
coreView (TyConApp tc tys) = expandSynTyConApp_maybe tc tys
coreView ty@(AppTy{}) = expandTyLamApp_maybe ty (const True)
coreView _ = Nothing
{-# INLINE coreView #-}

coreFullView :: IsTyVar tv kv => Type tv kv -> Type tv kv
coreFullView ty@(TyConApp tc _)
  | isTypeSynonymTyCon tc = core_full_view ty
coreFullView ty@(AppTy{}) = core_full_view ty
coreFullView ty = ty
{-# INLINE coreFullView #-}

core_full_view :: IsTyVar tv kv => Type tv kv -> Type tv kv
core_full_view ty
  | Just ty' <- coreView ty = core_full_view ty'
  | otherwise = ty

expandTyLamApp_maybe :: IsTyVar tv kv => Type tv kv -> (Type tv kv -> Bool) -> Maybe (Type tv kv)
expandTyLamApp_maybe ty pred = case split ty [] of
  (fn, args)
    | let arity = tyFunArity fn
    , args `saturates` arity
    , pred fn
      -> Just $! (expand_syn fn args)
  _ -> Nothing
  where
    split (AppTy ty arg) args = split ty (arg:args)
    split ty args = (ty, args)

tyFunArity :: Type tv kv -> Arity
tyFunArity = go 0
  where
    go i (TyLamTy _ ty) = go (i + 1) ty
    go i (BigTyLamTy _ ty) = go (i + 1) ty
    go i _ = i

expandSynTyConApp_maybe :: IsTyVar tv kv => TyCon tv kv -> [Type tv kv] -> Maybe (Type tv kv)
expandSynTyConApp_maybe tc arg_tys
  | Just rhs <- synTyConDefn_maybe tc
  , arg_tys `saturates` tyConArity tc
  = Just $! (expand_syn (asGenericTyKi rhs) arg_tys)
  | otherwise
  = Nothing

saturates :: [Type tv kv] -> Arity -> Bool
saturates _ 0 = True
saturates [] _ = False
saturates (_:tys) n = assert (n >= 0) $ saturates tys (n-1)

expand_syn :: IsTyVar tv kv => Type tv kv -> [Type tv kv] -> Type tv kv
expand_syn rhs arg_tys
  | null arg_tys = rhs
  | otherwise = go rhs empty_subst arg_tys
  where
    empty_subst = mkEmptyTvSubst in_scope
    in_scope = bimap mkInScopeSet mkInScopeSet $ case shallowVarsOfTypes arg_tys of
                                                   (tv, _, kv) -> (tv, kv)

    go (TyLamTy _ _) _ [] = pprPanic "expand_syn" (ppr rhs $$ ppr arg_tys)
    go (BigTyLamTy _ _) _ [] = pprPanic "expand_syn" (ppr rhs $$ ppr arg_tys)
    go ty subst [] = substTy subst ty
    go (TyLamTy tv ty) subst (arg:args) = go ty (extendTvSubst subst tv arg) args
    go (BigTyLamTy kv ty) subst (arg:args)
      | Embed ki <- arg = go ty (liftKvSubst subst (\s -> extendKvSubst s kv ki)) args
      | otherwise = pprPanic "expand_syn" (ppr rhs $$ ppr arg_tys)
    go ty subst args = mkAppTys (substTy subst ty) args

{- *********************************************************************
*                                                                      *
                      mapType
*                                                                      *
********************************************************************* -}

data TyCoMapper tv kv tv' kv' env m = TyCoMapper
  { tm_tyvar :: env -> tv -> m (Type tv' kv')
  , tm_covar :: env -> TyCoVar tv kv -> m (TypeCoercion tv' kv')
  , tm_hole :: env -> TypeCoercionHole tv kv -> m (TypeCoercion tv' kv')
  , tm_tybinder :: forall r. env -> tv -> ForAllFlag -> (env -> tv' -> m r) -> m r
  , tm_tylambinder :: forall r. env -> tv -> (env -> tv' -> m r) -> m r
  , tm_tylamkibinder :: forall r. env -> kv -> (env -> kv' -> m r) -> m r
  , tm_tycon :: TyCon tv kv -> m (TyCon tv' kv')
  , tm_mkcm :: MKiCoMapper kv kv' env m
  }

{-# INLINE mapTyCo #-}
mapTyCo
  :: (Monad m, VarHasKind tv kv, IsTyVar tv' kv') => TyCoMapper tv kv tv' kv' () m
  -> ( Type tv kv -> m (Type tv' kv')
     , [Type tv kv] -> m [Type tv' kv']
     , TypeCoercion tv kv -> m (TypeCoercion tv' kv')
     , [TypeCoercion tv kv] -> m [TypeCoercion tv' kv'] )
mapTyCo mapper = case mapTyCoX mapper of
  (go_ty, go_tys, go_co, go_cos) -> (go_ty (), go_tys (), go_co (), go_cos ())

{-# INLINE mapTyCoX #-}
mapTyCoX
  :: (Monad m, VarHasKind tv kv, IsTyVar tv' kv') => TyCoMapper tv kv tv' kv' env m
  -> ( env -> Type tv kv -> m (Type tv' kv')
     , env -> [Type tv kv] -> m [Type tv' kv']
     , env -> TypeCoercion tv kv -> m (TypeCoercion tv' kv')
     , env -> [TypeCoercion tv kv] -> m [TypeCoercion tv' kv'] )
mapTyCoX (TyCoMapper { tm_tyvar = tyvar
                     , tm_covar = covar
                     , tm_hole = cohole
                     , tm_tybinder = tybinder
                     , tm_tycon = tycon
                     , tm_tylambinder = tylambinder
                     , tm_tylamkibinder = kibinder
                     , tm_mkcm = mkcmapper })
  = (go_ty, go_tys, go_co, go_cos)
  where
    (go_mki, _, go_kco, _) = mapMKiCoX mkcmapper

    go_tys !_ [] = return []
    go_tys !env (ty:tys) = (:) <$> go_ty env ty <*> go_tys env tys

    go_ty !env (TyVarTy tv) = tyvar env tv
    go_ty !env (AppTy t1 t2) = mkAppTy <$> go_ty env t1 <*> go_ty env t2
    go_ty !env ty@(FunTy ki arg res) = do
      ki' <- go_mki env ki
      arg' <- go_ty env arg
      res' <- go_ty env res
      return $ FunTy ki' arg' res'
    go_ty !env ty@(TyConApp tc tys) = do
      tc' <- tycon tc
      mkTyConApp tc' <$> go_tys env tys
    go_ty !env (ForAllTy (Bndr tv vis) inner) = do
      tybinder env tv vis $ \env' tv' -> do
        inner' <- go_ty env' inner
        return $ ForAllTy (Bndr tv' vis) inner'
    go_ty !env (TyLamTy tv inner) = do
      tylambinder env tv $ \env' tv' -> do
        inner' <- go_ty env' inner
        return $ TyLamTy tv' inner'
    go_ty !env (BigTyLamTy kv inner) = do
      kibinder env kv $ \env' kv' -> do
        inner' <- go_ty env' inner
        return $ BigTyLamTy kv' inner'
    go_ty !env (Embed ki) = Embed <$> go_mki env ki
    go_ty !env (CastTy ty kco) = mkCastTy <$> go_ty env ty <*> go_kco env kco
    go_ty !env (KindCoercion kco) = KindCoercion <$> go_kco env kco

    go_cos !_ [] = return []
    go_cos !env (co:cos) = (:) <$> go_co env co <*> go_cos env cos

    go_co !env (TyRefl ty) = TyRefl <$> go_ty env ty
    go_co !env (GRefl ty kco) = mkGReflCo <$> go_ty env ty <*> go_kco env kco
    go_co !env (AppCo c1 c2) = mkAppCo <$> go_co env c1 <*> go_co env c2
    go_co !env (TyFunCo kco c1 c2)
      = mkTyFunCo <$> go_kco env kco <*> go_co env c1 <*> go_co env c2
    go_co !env (TyCoVarCo cv) = covar env cv
    go_co !env (TyHoleCo hole) = cohole env hole
    go_co !env (TySymCo co) = mkSymTyCo <$> go_co env co
    go_co !env (TyTransCo c1 c2) = mkTyTransCo <$> go_co env c1 <*> go_co env c2
    go_co !env (LRCo lr co) = mkLRTyCo lr <$> go_co env co
    go_co !env (LiftKCo kco) = LiftKCo <$> go_kco env kco
    go_co !env (TyConAppCo tc cos) = do
      tc' <- tycon tc
      mkTyConAppCo tc' <$> go_cos env cos

{- *********************************************************************
*                                                                      *
                      TyVarTy
*                                                                      *
********************************************************************* -}

isTyVarTy :: IsTyVar tv kv => Type tv kv -> Bool
isTyVarTy = isJust . getTyVar_maybe

getTyVar_maybe :: IsTyVar tv kv => Type tv kv -> Maybe tv
getTyVar_maybe = getTyVarNoView_maybe . coreFullView

getTcTyVar_maybe :: (IsTyVar tv kv, ToTcTyVarMaybe tv kv) => Type tv kv -> Maybe (TcTyVar kv)
getTcTyVar_maybe = getTyVar_maybe >=> toTcTyVar_maybe

getTyVarNoView_maybe :: Type tv kv -> Maybe tv
getTyVarNoView_maybe (TyVarTy tv) = Just tv
getTyVarNoView_maybe _ = Nothing

{- *********************************************************************
*                                                                      *
                      AppTy
*                                                                      *
********************************************************************* -}

mkAppTy :: Type tv kv -> Type tv kv -> Type tv kv
mkAppTy (TyConApp tc tys) ty2 = mkTyConApp tc (tys ++ [ty2])
mkAppTy ty1 ty2 = AppTy ty1 ty2

mkAppTys :: Type tv kv -> [Type tv kv] -> Type tv kv
mkAppTys ty1 [] = ty1
mkAppTys (TyConApp tc tys1) tys2 = mkTyConApp tc (tys1 ++ tys2)
mkAppTys ty1 tys2 = foldl' AppTy ty1 tys2

splitAppTy_maybe :: IsTyVar tv kv => Type tv kv -> Maybe (Type tv kv, Type tv kv)
splitAppTy_maybe = splitAppTyNoView_maybe . coreFullView

splitAppTy :: IsTyVar tv kv => Type tv kv -> (Type tv kv, Type tv kv)
splitAppTy ty = splitAppTy_maybe ty `orElse` pprPanic "splitAppTy" (ppr ty)

splitAppTyNoView_maybe :: IsTyVar tv kv => Type tv kv -> Maybe (Type tv kv, Type tv kv)
splitAppTyNoView_maybe (AppTy ty1 ty2) = Just (ty1, ty2)
splitAppTyNoView_maybe (FunTy ki ty1 ty2)
  | Just (tc, tys) <- funTyConAppTy_maybe ki ty1 ty2
  , Just (tys', ty') <- snocView tys
  = Just (TyConApp tc tys', ty')
splitAppTyNoView_maybe (TyConApp tc tys)
  | not (tyConMustBeSaturated tc) || tys `lengthExceeds` tyConArity tc
  , Just (tys', ty') <- snocView tys
  = Just (TyConApp tc tys', ty')
splitAppTyNoView_maybe _ = Nothing

tcSplitAppTyNoView_maybe :: IsTyVar tv kv => Type tv kv -> Maybe (Type tv kv, Type tv kv)
tcSplitAppTyNoView_maybe = splitAppTyNoView_maybe

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

funTyConAppTy_maybe
  :: IsTyVar tv kv =>
  MonoKind kv -> Type tv kv -> Type tv kv -> Maybe (TyCon tv kv, [Type tv kv])
funTyConAppTy_maybe ki arg res = Just ( asGenericTyKi fUNTyCon
                                      , [ Embed (typeMonoKind arg)
                                        , Embed (typeMonoKind res)
                                        , Embed ki
                                        , arg
                                        , res] )

piResultTys :: (HasDebugCallStack, IsTyVar tv kv) => Kind kv -> [Type tv kv] -> Kind kv
piResultTys ki [] = ki
piResultTys ki orig_args@(arg:args)
  | Mono mki <- ki
  = Mono $ monoPiResultTys mki orig_args
  | ForAllKi kv res <- ki
  , Embed mki <- arg
  = go (extendKvSubst init_subst kv mki) res args
  | otherwise
  = pprPanic "piResultTys2" (ppr ki $$ ppr orig_args)
  where
    init_subst = mkEmptyKvSubst $ mkInScopeSet $ kvs1 `unionVarSet` kvs2
      where
        kvs1 = varsOfKind ki
        (_, _, kvs2) = varsOfTypes orig_args

    -- go :: Subst -> Kind -> [Type] -> Kind
    go subst ki []
      | Mono ki' <- ki
      = Mono $ substMonoKiUnchecked subst ki'
      | otherwise
      = pprPanic "piResultTys3" (ppr ki)
    go subst ki all_args@(arg:args)
      | Mono (FunKi { fk_res = res }) <- ki
      = go subst (Mono res) args
      | ForAllKi kv res <- ki
      , Embed mono_ki <- arg
      = go (extendKvSubst subst kv mono_ki) res args
      | otherwise
      = pprPanic "piResultTys4" (ppr ki $$ ppr orig_args $$ ppr all_args)

monoPiResultTys :: IsTyVar tv kv => MonoKind kv -> [Type tv kv] -> MonoKind kv
monoPiResultTys ki [] = ki
monoPiResultTys ki orig_args@(arg:args)
  | FunKi { fk_res = res } <- ki
  = monoPiResultTys res args
  | otherwise
  = pprPanic "monoPiResultTys1" (ppr ki $$ ppr orig_args)

{- *********************************************************************
*                                                                      *
                      TyConApp
*                                                                      *
********************************************************************* -}

{-# INLINE tyConAppTyCon_maybe #-}
tyConAppTyCon_maybe :: IsTyVar tv kv => Type tv kv -> Maybe (TyCon tv kv)
tyConAppTyCon_maybe ty = case coreFullView ty of
  TyConApp tc _ -> Just tc
  FunTy {} -> Just (asGenericTyKi fUNTyCon)
  _ -> Nothing

splitTyConApp_maybe
  :: (HasDebugCallStack, IsTyVar tv kv)
  => Type tv kv -> Maybe (TyCon tv kv, [Type tv kv])
splitTyConApp_maybe ty = splitTyConAppNoView_maybe (coreFullView ty)

splitTyConAppNoView_maybe
  :: (HasDebugCallStack, IsTyVar tv kv)
  => Type tv kv -> Maybe (TyCon tv kv, [Type tv kv])
splitTyConAppNoView_maybe ty = case ty of
  FunTy { ft_kind = ki, ft_arg = arg, ft_res = res } -> funTyConAppTy_maybe ki arg res
  TyConApp tc tys -> Just (tc, tys)
  _ -> Nothing

tcSplitTyConApp_maybe
  :: (HasDebugCallStack, IsTyVar tv kv)
  => Type tv kv -> Maybe (TyCon tv kv, [Type tv kv])
tcSplitTyConApp_maybe ty = case coreFullView ty of
  FunTy { ft_kind = ki, ft_arg = arg, ft_res = res } -> funTyConAppTy_maybe ki arg res
  TyConApp tc tys -> Just (tc, tys)
  _ -> Nothing

{- *********************************************************************
*                                                                      *
                      CastTy
*                                                                      *
********************************************************************* -}

mkCastTy :: IsTyVar tv kv => Type tv kv -> KindCoercion kv -> Type tv kv
mkCastTy orig_ty co | isReflKiCo co = orig_ty
mkCastTy orig_ty co = mk_cast_ty orig_ty co

mkCastTyMCo :: IsTyVar tv kv => Type tv kv -> Maybe (KindCoercion kv) -> Type tv kv
mkCastTyMCo ty Nothing = ty
mkCastTyMCo ty (Just co) = ty `mkCastTy` co

mk_cast_ty :: IsTyVar tv kv => Type tv kv -> KindCoercion kv -> Type tv kv
mk_cast_ty orig_ty co = go orig_ty
  where
    -- go :: Type -> Type
    go ty | Just ty' <- coreView ty = go ty'
    go (CastTy ty co1) = mkCastTy ty (co1 `mkTransKiCo` co)
    go (ForAllTy bndr inner_ty) = ForAllTy bndr (inner_ty `mk_cast_ty` co)
    go _ = CastTy orig_ty co

tycoercionTypes
  :: (HasDebugCallStack, IsTyVar tv kv)
  => TypeCoercion tv kv -> Pair (Type tv kv)
tycoercionTypes co = Pair (tycoercionLType co) (tycoercionRType co)

tycoercionLType
  :: (HasDebugCallStack, IsTyVar tv kv)
  => TypeCoercion tv kv -> Type tv kv
tycoercionLType co = ty_coercion_lr_type CLeft co

tycoercionRType
  :: (HasDebugCallStack, IsTyVar tv kv)
  => TypeCoercion tv kv -> Type tv kv
tycoercionRType co = ty_coercion_lr_type CRight co

ty_coercion_lr_type
  :: (HasDebugCallStack, IsTyVar tv kv)
  => LeftOrRight -> TypeCoercion tv kv -> Type tv kv
ty_coercion_lr_type which orig_co = go orig_co
  where
    go (TyRefl ty) = ty
    go (GRefl ty kco) = pickLR which (ty, mkCastTy ty kco)
    go (TyConAppCo tc cos) = mkTyConApp tc (map go cos)
    go (AppCo co1 co2) = mkAppTy (go co1) (go co2)
    go (TyCoVarCo cv) = go_covar cv
    go (TyHoleCo h) = go_covar (tyCoHoleCoVar h)
    go (TySymCo co) = pickLR which (tycoercionRType co, tycoercionLType co)
    go (TyTransCo co1 co2) = pickLR which (go co1, go co2)
    go (LRCo lr co) = pickLR lr (splitAppTy (go co))
    go (LiftKCo kco) = Embed $ pickLR which (kicoercionLKind kco, kicoercionRKind kco)
    go (TyFunCo kco arg res)
      = FunTy { ft_kind = pickLR which (kicoercionLKind kco, kicoercionRKind kco)
              , ft_arg = go arg, ft_res = go res }

    go_covar cv = pickLR which (coVarLType cv, coVarRType cv)

coVarLType :: (HasDebugCallStack, IsTyVar tv kv) => TyCoVar tv kv -> Type tv kv
coVarLType cv | (ty1, _) <- coVarTypes cv = ty1

coVarRType :: (HasDebugCallStack, IsTyVar tv kv) => TyCoVar tv kv -> Type tv kv
coVarRType cv | (_, ty2) <- coVarTypes cv = ty2

coVarTypes :: (HasDebugCallStack, IsTyVar tv kv) => TyCoVar tv kv -> (Type tv kv, Type tv kv)
coVarTypes cv
  | Just (tc, [Embed _, ty1, ty2]) <- splitTyConApp_maybe (varType cv)
  = (ty1, ty2)
  | otherwise
  = pprPanic "coVarTypes, non coercion variable" (ppr cv $$ ppr (varType cv))

mkLRTyCo :: IsTyVar tv kv => LeftOrRight -> TypeCoercion tv kv -> TypeCoercion tv kv
mkLRTyCo lr co
  | Just ty <- isReflTyCo_maybe co
  = mkReflTyCo (pickLR lr (splitAppTy ty))
  | otherwise
  = LRCo lr co

{- *********************************************************************
*                                                                      *
        ForAllTy
*                                                                      *
********************************************************************* -}

splitForAllForAllTyBinders :: IsTyVar tv kv => Type tv kv -> ([ForAllBinder tv], Type tv kv)
splitForAllForAllTyBinders ty = split ty ty []
  where
    split _ (ForAllTy b res) bs = split res res (b : bs)
    split orig_ty ty bs | Just ty' <- coreView ty = split orig_ty ty' bs
    split orig_ty _ bs = (reverse bs, orig_ty)
{-# INLINE splitForAllForAllTyBinders #-}

splitForAllForAllTyBinder_maybe
  :: IsTyVar tv kv => Type tv kv -> Maybe (ForAllBinder tv, Type tv kv)
splitForAllForAllTyBinder_maybe ty
  | ForAllTy b inner_ty <- coreFullView ty = Just (b, inner_ty)
  | otherwise = Nothing

splitForAllInvisTyBinders :: IsTyVar tv kv => Type tv kv -> ([tv], Type tv kv)
splitForAllInvisTyBinders ty = split ty ty []
  where
    split _ (ForAllTy (Bndr tv Specified) ty) tvs = split ty ty (tv:tvs)
    split orig_ty ty tvs | Just ty' <- coreView ty = split orig_ty ty' tvs
    split orig_ty _ tvs = (reverse tvs, orig_ty)

splitTyLamTyBinders :: IsTyVar tv kv => Type tv kv -> ([tv], Type tv kv)
splitTyLamTyBinders ty = split ty ty []
  where
    split _ (TyLamTy b res) bs = split res res (b : bs)
    split orig_ty ty bs | Just ty' <- coreView ty = split orig_ty ty' bs
    split orig_ty _ bs = (reverse bs, orig_ty)

splitBigLamTyBinders :: IsTyVar tv kv => Type tv kv -> ([kv], Type tv kv)
splitBigLamTyBinders ty = split ty ty []
  where
    split _ (BigTyLamTy b res) bs = split res res (b : bs)
    split orig_ty ty bs | Just ty' <- coreView ty = split orig_ty ty' bs
    split orig_ty _ bs = (reverse bs, orig_ty)

splitForAllTyVars :: IsTyVar tv kv => Type tv kv -> ([tv], Type tv kv)
splitForAllTyVars ty = split ty ty []
  where
    split _ (ForAllTy (Bndr tv _) ty) tvs = split ty ty (tv:tvs)
    split orig_ty ty tvs | Just ty' <- coreView ty = split orig_ty ty' tvs
    split orig_ty _ tvs = (reverse tvs, orig_ty)

isForAllTy :: IsTyVar tv kv => Type tv kv -> Bool
isForAllTy ty
  | ForAllTy {} <- coreFullView ty = True
  | otherwise = False

isTauTy :: IsTyVar tv kv => Type tv kv -> Bool
isTauTy ty | Just ty' <- coreView ty = isTauTy ty'
isTauTy (TyVarTy _) = True
isTauTy (TyConApp tc tys) = all isTauTy tys && isTauTyCon tc
isTauTy (AppTy a b) = isTauTy a && isTauTy b
isTauTy (FunTy _ a b) = isTauTy a && isTauTy b
isTauTy (ForAllTy {}) = False
isTauTy (TyLamTy _ ty) = isTauTy ty
isTauTy other = pprPanic "isTauTy" (ppr other)

isForgetfulTy :: IsTyVar tv kv => Type tv kv -> Bool
isForgetfulTy (TyVarTy _) = False
isForgetfulTy (TyConApp tc tys) = isForgetfulSynTyCon tc || any isForgetfulTy tys
isForgetfulTy (AppTy a b) = isForgetfulTy a || isForgetfulTy b
isForgetfulTy (FunTy _ a b) = isForgetfulTy a || isForgetfulTy b
isForgetfulTy (ForAllTy (Bndr tv _) ty)
  = (not $ tv `elemVarSet` (fstOf3 $ varsOfType ty)) || isForgetfulTy ty
isForgetfulTy (TyLamTy tv ty) = (not $ tv `elemVarSet` (fstOf3 $ varsOfType ty)) || isForgetfulTy ty
isForgetfulTy other = pprPanic "isForgetfulTy" (ppr other)

splitPiTys :: IsTyVar tv kv => Type tv kv -> ([PiTyBinder tv kv], Type tv kv)
splitPiTys ty = split ty ty []
  where
    split _ (ForAllTy b res) bs = split res res (NamedTy b : bs)
    split _ (FunTy { ft_arg = arg, ft_res = res }) bs = split res res (AnonTy arg : bs)
    split orig_ty ty bs | Just ty' <- coreView ty = split orig_ty ty' bs
    split orig_ty _ bs = (reverse bs, orig_ty)

{- *********************************************************************
*                                                                      *
            Type families
*                                                                      *
********************************************************************* -}

{- NOTE:
We do note need the type to be KnotTied.
This is because we do not have recursive things the same way haskell does.
-}
buildSynTyCon
  :: Name
  -> Kind KiVar
  -> Arity
  -> Type (TyVar KiVar) KiVar
  -> TyCon (TyVar KiVar) KiVar
buildSynTyCon name kind arity rhs
  = mkSynonymTyCon name kind arity rhs is_tau is_forgetful is_concrete
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

typeKind :: (HasDebugCallStack, IsTyVar tv kv) => Type tv kv -> Kind kv
typeKind (BigTyLamTy kv res) = mkForAllKi kv (typeKind res)
typeKind (TyConApp tc []) = tyConKind tc
typeKind ty = Mono $ typeMonoKind ty

typeMonoKind :: (HasDebugCallStack, IsTyVar tv kv) => Type tv kv -> MonoKind kv
typeMonoKind (TyConApp tc tys) = handle_non_mono (piResultTys (tyConKind tc) tys)
                                 $ \ki -> vcat [ ppr tc <+> colon <+> ppr ki
                                                , ppr tys ]
  
typeMonoKind (FunTy { ft_kind = kind }) = kind
typeMonoKind (TyVarTy tyvar) = varKind tyvar
typeMonoKind (AppTy fun arg)
  = go fun [arg]
  where
    go (AppTy fun arg) args = go fun (arg:args)
    go fun args = handle_non_mono (piResultTys (typeKind fun) args)
                  $ \ki -> vcat [ ppr fun <+> colon <+> ppr ki
                                , ppr args ]
typeMonoKind ty@(ForAllTy {})
  = let (tvs, body) = splitForAllTyVars ty
        body_kind = typeMonoKind body
    in assertPpr (not (null tvs)) (ppr ty) body_kind
typeMonoKind ty@(TyLamTy tv res) =
  let tvKind = varKind tv
      res_kind = typeMonoKind res
      flag = chooseFunKiFlag tvKind res_kind
  in mkFunKi flag tvKind res_kind
typeMonoKind ty@(BigTyLamTy _ _) = pprPanic "typeMonoKind" (ppr ty)
typeMonoKind ty@(Embed _) = pprPanic "typeMonoKind" (ppr ty)
typeMonoKind (CastTy _ co) = kicoercionRKind co
typeMonoKind (KindCoercion kco) = kiCoercionKind kco

handle_non_mono :: Kind kv -> (Kind kv -> SDoc) -> MonoKind kv
handle_non_mono ki doc = case ki of
                           Mono ki -> ki
                           other -> pprPanic "typeMonoKind" (doc other)

{- *********************************************************************
*                                                                      *
                    Space-saving construction
*                                                                      *
********************************************************************* -}

mkTyConApp :: TyCon tv kv -> [Type tv kv] -> Type tv kv
mkTyConApp tycon [] = mkTyConTy tycon
mkTyConApp tycon tys = TyConApp tycon tys

mkTyConAppCo
  :: (HasDebugCallStack, IsTyVar tv kv)
  => TyCon tv kv -> [TypeCoercion tv kv] -> TypeCoercion tv kv
mkTyConAppCo tc cos
  | Just co <- tyConAppFunCo_maybe tc cos
  = co
  | ExpandsSyn tv_co_prs rhs_ty leftover_cos <- expandSynTyCon_maybe tc cos
  = panic "mkAppCos (liftTyCoSubst (mkTyLiftingContext tv_co_prs) rhs_ty) leftover_cos"
  | Just tys <- traverse isReflTyCo_maybe cos
  = mkReflTyCo (mkTyConApp tc tys)
  | otherwise
  = TyConAppCo tc cos

tyConAppFunCo_maybe
  :: (HasDebugCallStack, IsTyVar tv kv)
  => TyCon tv kv -> [TypeCoercion tv kv] -> Maybe (TypeCoercion tv kv)
tyConAppFunCo_maybe tc cos
  | Just (LiftKCo arg_ki, LiftKCo res_ki, LiftKCo fun_ki, arg, res)
    <- ty_con_app_fun_maybe tc cos
  = Just (mkTyFunCo fun_ki arg res)
  | otherwise
  = Nothing

mkTyFunCo
  :: IsTyVar tv kv
  => KindCoercion kv
  -> TypeCoercion tv kv
  -> TypeCoercion tv kv
  -> TypeCoercion tv kv
mkTyFunCo kco arg_co res_co
  | Just ty1 <- isReflTyCo_maybe arg_co
  , Just ty2 <- isReflTyCo_maybe res_co
  , Just k <- isReflKiCo_maybe kco
  = mkReflTyCo (mkFunTy k ty1 ty2)
  | otherwise
  = TyFunCo { tfco_ki = kco
            , tfco_arg = arg_co
            , tfco_res = res_co }

mkAppCo :: IsTyVar tv kv => TypeCoercion tv kv -> TypeCoercion tv kv -> TypeCoercion tv kv
mkAppCo co arg
  | Just ty1 <- isReflTyCo_maybe co
  , Just ty2 <- isReflTyCo_maybe arg
  = mkReflTyCo (mkAppTy ty1 ty2)
  | Just ty1 <- isReflTyCo_maybe co
  , Just (tc, tys) <- splitTyConApp_maybe ty1
  = mkTyConAppCo tc ((mkReflTyCo <$> tys) ++ [arg])
mkAppCo (TyConAppCo tc args) arg
  = mkTyConAppCo tc (args ++ [arg])
mkAppCo co arg = AppCo co arg

mkAppCos :: IsTyVar tv kv => TypeCoercion tv kv -> [TypeCoercion tv kv] -> TypeCoercion tv kv
mkAppCos co1 cos = foldl' mkAppCo co1 cos

{- *********************************************************************
*                                                                      *
                    Type Coercions
*                                                                      *
********************************************************************* -}

mkTyEqPred :: IsTyVar tv kv => Type tv kv -> Type tv kv -> Type tv kv
mkTyEqPred ty1 ty2
  = mkTyConApp (asGenericTyKi eqTyCon) [Embed ki1, Embed ki2, ty1, ty2]
  where
    ki1 = typeMonoKind ty1
    ki2 = typeMonoKind ty2

decomposeFunCo
  :: (HasDebugCallStack, IsKiVar kv)
  => KindCoercion kv
  -> (KindCoercion kv, KindCoercion kv)
decomposeFunCo (FunCo { fco_arg = co1, fco_res = co2 })
  = (co1, co2)
decomposeFunCo co
  = assertPpr all_ok (ppr co)
    $ (mkSelCo (SelFun SelArg) co, mkSelCo (SelFun SelRes) co)
  where
    (_, Pair k1 k2) = kiCoercionParts co
    all_ok = isMonoFunKi k1 && isMonoFunKi k2

decomposePiCos
  :: (HasDebugCallStack, IsTyVar tv kv)
  => KindCoercion kv -> (KiPredCon, Pair (MonoKind kv))
  -> [Type tv kv]
  -> ([KindCoercion kv], KindCoercion kv)
decomposePiCos orig_kco (EQKi, (Pair orig_ki1 orig_ki2)) orig_args
  = go [] orig_ki1 orig_kco orig_ki2 orig_args
  where
    go acc_arg_cos k1 co k2 (ty:tys)
      | Just (af1, _, r1) <- splitMonoFunKi_maybe k1
      , Just (af2, _, r2) <- splitMonoFunKi_maybe k2
      , af1 == af2
      = let (sym_arg_co, res_co) = decomposeFunCo co
            arg_co = mkSymKiCo sym_arg_co
        in go (arg_co : acc_arg_cos) r1 res_co r2 tys

    go acc_arg_cos _ co _ _ = (reverse acc_arg_cos, co)
decomposePiCos co stuff args = pprPanic "decomposePiCos not EQKi"
                               $ vcat [ ppr co, ppr stuff, ppr args ]

setCoHoleType :: IsTyVar tv kv => TypeCoercionHole tv kv -> Type tv kv -> TypeCoercionHole tv kv
setCoHoleType h t = setTyCoHoleCoVar h (setVarType (tyCoHoleCoVar h) t)

setTyCoHoleCoVar
  :: IsTyVar tv kv => TypeCoercionHole tv kv -> TyCoVar tv kv -> TypeCoercionHole tv kv
setTyCoHoleCoVar h cv = h { tch_co_var = cv }

castCoercionKind2
  :: IsTyVar tv kv
  => TypeCoercion tv kv
  -> Type tv kv -> Type tv kv
  -> KindCoercion kv -> KindCoercion kv
  -> TypeCoercion tv kv 
castCoercionKind2 g t1 t2 h1 h2
  = mkCoherenceRightCo t2 h2 (mkCoherenceLeftCo t1 h1 g)

castCoercionKind1
  :: IsTyVar tv kv
  => TypeCoercion tv kv -> Type tv kv -> Type tv kv -> KindCoercion kv -> TypeCoercion tv kv
castCoercionKind1 g t1 t2 h
  = case g of
      TyRefl {} -> mkReflTyCo (mkCastTy t2 h)
      GRefl _ kco -> mkGReflCo (mkCastTy t1 h) (mkSymKiCo h `mkTransKiCo` kco `mkTransKiCo` h)
      _ -> castCoercionKind2 g t1 t2 h h

