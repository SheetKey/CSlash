{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Type
  ( Type(..), TypeCoercion(..), TypeCoercionHole(..), PredType, ForAllFlag(..) -- , FunTyFlag(..)
  , TyVar, TyCoVar, ForAllBinder, MTypeCoercion(..)
  , KnotTied

  , typeSize

  , varsOfType

  , mkFunTy

  , mkForAllTy, mkForAllKiCo, mkForAllKiCos, mkBigLamTy
  , mkInfForAllTy, mkInfForAllTys

  , mkTyVarTy, mkTyVarTys

  , mkAppTy, mkAppTys

  , mkTyConTy

  , mkTyCoVarCo, mkTyHoleCo

  , mkBigLamTys

  , mkInvisForAllTys

  , isReflTyCo, mkSymTyCo, mkReflTyCo, mkTyTransCo

  , binderVar, binderVars

  , module CSlash.Core.Type
  , module CSlash.Core.Rep
  ) where

import CSlash.Types.Basic

import CSlash.Cs.Pass

import {-# SOURCE #-} CSlash.Core.Subst
import CSlash.Core.Rep
import CSlash.Core.Type.FVs

import CSlash.Core.Kind
import CSlash.Core.Kind.Compare
-- import CSlash.Core.Kind.FVs

import CSlash.Types.Var.TyVar
import CSlash.Types.Var.KiVar
import CSlash.Types.Var.CoVar
import CSlash.Types.Var.Class
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

{- **********************************************************************
*                                                                       *
                        Type
*                                                                       *
********************************************************************** -}

type PredType = Type

type KnotTied ty = ty

{- *********************************************************************
*                                                                      *
                      TyVarTy
*                                                                      *
********************************************************************* -}

isTyVarTy :: HasPass p pass => Type p -> Bool
isTyVarTy = isJust . getTyVar_maybe

getTyVar_maybe :: HasPass p pass => Type p -> Maybe (TyVar p)
getTyVar_maybe = getTyVarNoView_maybe . coreFullView

getTcTyVar_maybe :: Type Tc -> Maybe TcTyVar 
getTcTyVar_maybe = getTyVar_maybe >=> toTcTyVar_maybe

getTyVarNoView_maybe :: Type p -> Maybe (TyVar p)
getTyVarNoView_maybe (TyVarTy tv) = Just tv
getTyVarNoView_maybe _ = Nothing

{- *********************************************************************
*                                                                      *
                      AppTy
*                                                                      *
********************************************************************* -}

mkAppTy :: Type p -> Type p -> Type p
mkAppTy (TyConApp tc tys) ty2 = mkTyConApp tc (tys ++ [ty2])
mkAppTy ty1 ty2 = AppTy ty1 ty2

splitAppTy_maybe :: HasPass p pass => Type p -> Maybe (Type p, Type p)
splitAppTy_maybe = splitAppTyNoView_maybe . coreFullView

splitAppTy :: HasPass p pass => Type p -> (Type p, Type p)
splitAppTy ty = splitAppTy_maybe ty `orElse` pprPanic "splitAppTy" (ppr ty)

splitAppTyNoView_maybe :: HasPass p pass => Type p -> Maybe (Type p, Type p)
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

tcSplitAppTyNoView_maybe :: HasPass p pass => Type p -> Maybe (Type p, Type p)
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

mkFunctionType :: HasDebugCallStack => Type p -> MonoKind p -> Type p -> Type p
mkFunctionType arg_ty ki res_ty
  = FunTy { ft_kind = ki, ft_arg = arg_ty, ft_res = res_ty }

splitFunTy :: HasPass p pass => Type p -> (Type p, MonoKind p, Type p)
splitFunTy ty = case splitFunTy_maybe ty of
  Just (arg, ki, res) -> (arg, ki, res)
  Nothing -> pprPanic "splitFunTy" (ppr ty)

{-# INLINE splitFunTy_maybe #-}
splitFunTy_maybe :: HasPass p pass => Type p -> Maybe (Type p, MonoKind p, Type p)
splitFunTy_maybe ty
  | FunTy ki arg res <- coreFullView ty = Just (arg, ki, res)
  | otherwise = Nothing

funTyConAppTy_maybe
  :: HasPass p pass => MonoKind p -> Type p -> Type p -> Maybe (TyCon p, [Type p])
funTyConAppTy_maybe ki arg res = Just ( fUNTyCon
                                      , [ Embed (typeMonoKind arg)
                                        , Embed (typeMonoKind res)
                                        , Embed ki
                                        , arg
                                        , res] )

funResultTy :: (HasDebugCallStack, HasPass p pass) => Type p -> Type p
funResultTy ty
  | FunTy { ft_res = res } <- coreFullView ty = res
  | otherwise = pprPanic "funResultTy" (ppr ty)

funArgTy :: (HasDebugCallStack, HasPass p pass) => Type p -> Type p
funArgTy ty
  | FunTy { ft_arg = arg } <- coreFullView ty = arg
  | otherwise = pprPanic "funArgTy" (ppr ty)

piResultTy :: (HasDebugCallStack, HasPass p pass) => Type p -> Type p -> Type p
piResultTy ty arg = case piResultTy_maybe ty arg of
                      Just res -> res
                      Nothing -> pprPanic "piResultTy" (ppr ty $$ ppr arg)

piResultTy_maybe :: (HasPass p pass) => Type p -> Type p -> Maybe (Type p)
piResultTy_maybe ty (Embed arg) = case coreFullView ty of
  FunTy { ft_res = res } -> Just res
  BigTyLamTy kv res ->
    let empty_subst = mkEmptySubst (varsOfType res) (emptyVarSet, emptyVarSet, varsOfMonoKind arg)
    in Just $ substTy (extendKvSubst empty_subst kv arg) res
  _ -> Nothing
piResultTy_maybe ty (KindCoercion arg) = case coreFullView ty of
  FunTy { ft_res = res }  -> Just res
  ForAllKiCo kcv res ->
    let empty_subst = mkEmptySubst (varsOfType res)
                      ((\(kcv, kv) -> (emptyVarSet, kcv, kv)) $ varsOfKiCo arg)
    in Just $ substTy (extendKCvSubst empty_subst kcv arg) res
  _ -> Nothing
piResultTy_maybe ty arg = case coreFullView ty of
  FunTy { ft_res = res } -> Just res
  ForAllTy tv res ->
    let empty_subst = mkEmptySubst (varsOfType res) (varsOfType arg)
    in Just $ substTy (extendTvSubst empty_subst (binderVar tv) arg) res
  _ -> Nothing

piResultTys :: (HasDebugCallStack, HasPass p pass) => Type p -> [Type p] -> Type p
piResultTys ty [] = ty
piResultTys ty orig_args@(arg:args)
  | FunTy { ft_res = res } <- ty -- should we check that the arg is not a Tv, KiCo, Kind?
  = piResultTys res args
  | ForAllTy (Bndr tv _) res <- ty -- should we check the arg isn't a KiCo or Kind? 
  = go (extendTvSubst init_subst tv arg) res args
  | ForAllKiCo kcv res <- ty
  , KindCoercion kco <- arg
  = go (extendKCvSubst init_subst kcv kco) res args
  | BigTyLamTy kv res <- ty
  , Embed ki <- arg
  = go (extendKvSubst init_subst kv ki) res args
  | Just ty' <- coreView ty
  = piResultTys ty' orig_args
  | otherwise
  = pprPanic "piResultTys1" (ppr ty $$ ppr orig_args)
  where
    init_subst = mkEmptySubst (varsOfType ty) (varsOfTypes orig_args)

    go subst ty [] = substTyUnchecked subst ty
    go subst ty all_args@(arg:args)
      | FunTy { ft_res = res } <- ty
      = go subst res args
      | ForAllTy (Bndr tv _) res <- ty
      = go (extendTvSubst subst tv arg) res args
      | ForAllKiCo kcv res <- ty
      , KindCoercion kco <- arg
      = go (extendKCvSubst subst kcv kco) res args
      | BigTyLamTy kv res <- ty
      , Embed ki <- arg
      = go (extendKvSubst subst kv ki) res args
      | Just ty' <- coreView ty
      = go subst ty' all_args
      | not (isEmptySubst subst)
      = go init_subst (substTy subst ty) all_args
      | otherwise
      = pprPanic "piResultTys2" (ppr ty $$ ppr orig_args $$ ppr all_args)

piKiResultTys :: (HasDebugCallStack, HasPass p pass) => Kind p -> [Type p] -> Kind p
piKiResultTys ki [] = ki
piKiResultTys ki orig_args@(arg:args)
  | Mono mki <- ki
  = Mono $ monoPiKiResultTys mki orig_args
  | ForAllKi kv res <- ki
  , Embed mki <- arg
  = go (extendKvSubst init_subst kv mki) res args
  | otherwise
  = pprPanic "piKiResultTys2" (ppr ki $$ ppr orig_args)
  where
    init_subst = mkEmptySubst (emptyVarSet, emptyVarSet, varsOfKind ki) (varsOfTypes orig_args)

    -- go :: Subst -> Kind -> [Type] -> Kind
    go subst ki []
      | Mono ki' <- ki
      = Mono $ substMonoKiUnchecked subst ki'
      | otherwise
      = pprPanic "piKiResultTys3" (ppr ki)
    go subst ki all_args@(arg:args)
      | Mono (FunKi { fk_res = res }) <- ki
      = go subst (Mono res) args
      | ForAllKi kv res <- ki
      , Embed mono_ki <- arg
      = go (extendKvSubst subst kv mono_ki) res args
      | otherwise
      = pprPanic "piKiResultTys4" (ppr ki $$ ppr orig_args $$ ppr all_args)

monoPiKiResultTys :: HasPass p pass => MonoKind p -> [Type p] -> MonoKind p
monoPiKiResultTys ki [] = ki
monoPiKiResultTys ki orig_args@(arg:args)
  | FunKi { fk_res = res } <- ki
  = monoPiKiResultTys res args
  | otherwise
  = pprPanic "monoPiKiResultTys1" (ppr ki $$ ppr orig_args)

{- *********************************************************************
*                                                                      *
                      TyConApp
*                                                                      *
********************************************************************* -}

{-# INLINE tyConAppTyCon_maybe #-}
tyConAppTyCon_maybe :: HasPass p pass => Type p -> Maybe (TyCon p)
tyConAppTyCon_maybe ty = case coreFullView ty of
  TyConApp tc _ -> Just tc
  FunTy {} -> Just fUNTyCon
  _ -> Nothing

tyConAppArgs_maybe :: HasPass p pass => Type p -> Maybe [Type p]
tyConAppArgs_maybe ty = case splitTyConApp_maybe ty of
                          Just (_, tys) -> Just tys
                          Nothing -> Nothing

tyConAppArgs :: (HasDebugCallStack, HasPass p pass) => Type p -> [Type p]
tyConAppArgs ty = tyConAppArgs_maybe ty `orElse` pprPanic "tyConAppArgs" (ppr ty)

splitTyConApp_maybe
  :: (HasDebugCallStack, HasPass p pass)
  => Type p -> Maybe (TyCon p, [Type p])
splitTyConApp_maybe ty = splitTyConAppNoView_maybe (coreFullView ty)

splitTyConAppNoView_maybe
  :: (HasDebugCallStack, HasPass p pass)
  => Type p -> Maybe (TyCon p, [Type p])
splitTyConAppNoView_maybe ty = case ty of
  FunTy { ft_kind = ki, ft_arg = arg, ft_res = res } -> funTyConAppTy_maybe ki arg res
  TyConApp tc tys -> Just (tc, tys)
  _ -> Nothing

tcSplitTyConApp_maybe
  :: (HasDebugCallStack, HasPass p pass)
  => Type p -> Maybe (TyCon p, [Type p])
tcSplitTyConApp_maybe ty = case coreFullView ty of
  FunTy { ft_kind = ki, ft_arg = arg, ft_res = res } -> funTyConAppTy_maybe ki arg res
  TyConApp tc tys -> Just (tc, tys)
  _ -> Nothing

{- *********************************************************************
*                                                                      *
                      CastTy
*                                                                      *
********************************************************************* -}

mkCastTy :: HasPass p pass => Type p -> KindCoercion p -> Type p
mkCastTy orig_ty co | isReflKiCo co = orig_ty
mkCastTy orig_ty co = mk_cast_ty orig_ty co

mkCastTyMCo :: HasPass p pass => Type p -> Maybe (KindCoercion p) -> Type p
mkCastTyMCo ty Nothing = ty
mkCastTyMCo ty (Just co) = ty `mkCastTy` co

mk_cast_ty :: HasPass p pass => Type p -> KindCoercion p -> Type p
mk_cast_ty orig_ty co = go orig_ty
  where
    -- go :: Type -> Type
    go ty | Just ty' <- coreView ty = go ty'
    go (CastTy ty co1) = mkCastTy ty (co1 `mkTransKiCo` co)
    go (ForAllTy bndr inner_ty) = ForAllTy bndr (inner_ty `mk_cast_ty` co)
    go _ = CastTy orig_ty co

tycoercionTypes
  :: (HasDebugCallStack, HasPass p pass)
  => TypeCoercion p -> Pair (Type p)
tycoercionTypes co = Pair (tycoercionLType co) (tycoercionRType co)

tycoercionLType
  :: (HasDebugCallStack, HasPass p pass)
  => TypeCoercion p -> Type p
tycoercionLType co = ty_coercion_lr_type CLeft co

tycoercionRType
  :: (HasDebugCallStack, HasPass p pass)
  => TypeCoercion p -> Type p
tycoercionRType co = ty_coercion_lr_type CRight co

tycoercionType
  :: (HasDebugCallStack, HasPass p pass)
  => TypeCoercion p -> Type p
tycoercionType co = case tycoercionTypes co of
  Pair ty1 ty2 -> mkTyEqPred ty1 ty2

ty_coercion_lr_type
  :: forall p pass. (HasDebugCallStack, HasPass p pass)
  => LeftOrRight -> TypeCoercion p -> Type p
ty_coercion_lr_type @p @pass which orig_co = go orig_co
  where
    go :: TypeCoercion p -> Type p
    go (TyRefl ty) = ty
    go (GRefl ty kco) = pickLR which (ty, mkCastTy ty kco)
    go (TyConAppCo tc cos) = mkTyConApp tc (map go cos)
    go (AppCo co1 co2) = mkAppTy (go co1) (go co2)
    go (TyCoVarCo cv) = go_covar cv
    go (TyHoleCo h) = case csPass @pass of
                        Tc -> go_covar (TcCoVar $ tyCoHoleCoVar h)
                        _ -> panic "unreachable"
    go (TySymCo co) = pickLR which (tycoercionRType co, tycoercionLType co)
    go (TyTransCo co1 co2) = pickLR which (go co1, go co2)
    go (LRCo lr co) = pickLR lr (splitAppTy (go co))
    go (LiftKCo kco) = Embed $ pickLR which (kicoercionLKind kco, kicoercionRKind kco)
    go (TyFunCo kco arg res)
      = FunTy { ft_kind = pickLR which (kicoercionLKind kco, kicoercionRKind kco)
              , ft_arg = go arg, ft_res = go res }
    go co@(ForAllCo { tfco_tv = tv1, tfco_visL = visL, tfco_visR = visR
                    , tfco_tv_kind_co = kco, tfco_body = co1 })
      = case which of
          CLeft -> mkForAllTy (Bndr tv1 visL) (go co1)
          CRight | isReflKiCo kco -> mkForAllTy (Bndr tv1 visR) (go co1)
                 | otherwise -> pprPanic "ForAllCo" (ppr co)
    go co@(ForAllCoCo { tfcoco_kcv = kcv1, tfcoco_kcv_kind_co = kco, tfcoco_body = co1 })
      = case which of
          CLeft -> mkForAllKiCo kcv1 (go co1)
          CRight | isReflKiCo kco -> mkForAllKiCo kcv1 (go co1)
                 | otherwise -> pprPanic "ForAllCoCo" (ppr co)

    go_covar :: TyCoVar p -> Type p
    go_covar cv = pickLR which (coVarLType cv, coVarRType cv)

coVarLType :: (HasDebugCallStack, HasPass p pass) => TyCoVar p -> Type p
coVarLType cv | (ty1, _) <- coVarTypes cv = ty1

coVarRType :: (HasDebugCallStack, HasPass p pass) => TyCoVar p -> Type p
coVarRType cv | (_, ty2) <- coVarTypes cv = ty2

coVarTypes :: (HasDebugCallStack, HasPass p pass) => TyCoVar p -> (Type p, Type p)
coVarTypes cv
  | Just (tc, [Embed _, ty1, ty2]) <- splitTyConApp_maybe (varType cv)
  = (ty1, ty2)
  | otherwise
  = pprPanic "coVarTypes, non coercion variable" (ppr cv $$ ppr (varType cv))

mkLRTyCo :: HasPass p pass => LeftOrRight -> TypeCoercion p -> TypeCoercion p
mkLRTyCo lr co
  | Just ty <- isReflTyCo_maybe co
  = mkReflTyCo (pickLR lr (splitAppTy ty))
  | otherwise
  = LRCo lr co

{- *********************************************************************
*                                                                      *
        ForAllCo
*                                                                      *
********************************************************************* -}

mkForAllCo
  :: (HasDebugCallStack, HasPass p pass)
  => TyVar p -> ForAllFlag -> ForAllFlag -> KindCoercion p -> TypeCoercion p -> TypeCoercion p
mkForAllCo v visL visR kind_co co
  | Just ty <- isReflTyCo_maybe co
  , isReflKiCo kind_co
  , visL `eqForAllVis` visR
  = mkReflTyCo (mkForAllTy (Bndr v visL) ty)
  | otherwise
  = mkForAllCo_NoRefl v visL visR kind_co co

mkHomoForAllCos :: HasPass p pass => [ForAllBinder (TyVar p)] -> TypeCoercion p -> TypeCoercion p
mkHomoForAllCos vs orig_co
  | Just ty <- isReflTyCo_maybe orig_co
  = mkReflTyCo (mkForAllTys vs ty)
  | otherwise
  = foldr go orig_co vs
  where
    go (Bndr var vis) co = mkForAllCo_NoRefl var vis vis (mkReflKiCo (varKind var)) co

mkForAllCo_NoRefl
  :: HasPass p pass
  => TyVar p -> ForAllFlag -> ForAllFlag -> KindCoercion p -> TypeCoercion p -> TypeCoercion p
mkForAllCo_NoRefl tv visL visR kco co
  = assertGoodForAllCo tv visL visR kco co $
    assertPpr (not (isReflTyCo co && isReflKiCo kco && visL == visR)) (ppr co) $
    ForAllCo { tfco_tv = tv, tfco_visL = visL, tfco_visR = visR
             , tfco_tv_kind_co = kco, tfco_body = co }

assertGoodForAllCo
  :: (HasDebugCallStack, HasPass p pass)
  => TyVar p -> ForAllFlag -> ForAllFlag -> KindCoercion p -> TypeCoercion p -> a -> a
assertGoodForAllCo tv visL visR kind_co co = assertPpr (tv_kind `eqMonoKind` kind_co_lkind) doc
  where
    tv_kind = varKind tv
    kind_co_lkind = kicoercionLKind kind_co

    doc = vcat [ text "Var:" <+> ppr tv <+> colon <+> ppr tv_kind
               , text "Vis:" <+> ppr visL <+> ppr visR
               , text "kind_co:" <+> ppr kind_co
               , text "kind_co_lkind" <+> ppr kind_co_lkind
               , text "body_co" <+> ppr co ]

mkForAllCoCo
  :: (HasDebugCallStack, HasPass p pass)
  => KiCoVar p -> KindCoercion p -> TypeCoercion p -> TypeCoercion p
mkForAllCoCo kcv kind_co co
  | Just ty <- isReflTyCo_maybe co
  , isReflKiCo kind_co
  = mkReflTyCo (mkForAllKiCo kcv ty)
  | otherwise
  = mkForAllCoCo_NoRefl kcv kind_co co

mkHomoForAllCoCos :: HasPass p pass => [KiCoVar p] -> TypeCoercion p -> TypeCoercion p
mkHomoForAllCoCos vs orig_co
  | Just ty <- isReflTyCo_maybe orig_co
  = mkReflTyCo (mkForAllKiCos vs ty)
  | otherwise
  = foldr go orig_co vs
  where
    go var co = mkForAllCoCo_NoRefl var (mkReflKiCo (varKind var)) co

mkForAllCoCo_NoRefl
  :: HasPass p pass => KiCoVar p -> KindCoercion p -> TypeCoercion p -> TypeCoercion p
mkForAllCoCo_NoRefl kcv kind_co co
  = assertGoodForAllCoCo kcv kind_co co $
    assertPpr (not (isReflTyCo co && isReflKiCo kind_co)) (ppr co) $
    ForAllCoCo { tfcoco_kcv = kcv
               , tfcoco_kcv_kind_co = kind_co
               , tfcoco_body = co }

assertGoodForAllCoCo
  :: (HasDebugCallStack, HasPass p pass)
  => KiCoVar p -> KindCoercion p -> TypeCoercion p -> a -> a
assertGoodForAllCoCo kcv kind_co co =
  assertPpr (kcv_kind `eqMonoKind` kind_co_lkind) doc
  . assertPpr (almostDevoidKiCoVarOfTyCo kcv co) doc
  where
    kcv_kind = varKind kcv
    kind_co_lkind = kicoercionLKind kind_co

    doc = vcat [ text "Var:" <+> ppr kcv <+> colon <+> ppr kcv_kind
               , text "kind_co:" <+> ppr kind_co
               , text "kind_co_lkind" <+> ppr kind_co_lkind
               , text "body_co" <+> ppr co ]

{- *********************************************************************
*                                                                      *
        ForAllTy
*                                                                      *
********************************************************************* -}

splitForAllTyVar_maybe :: HasPass p pass => Type p -> Maybe (TyVar p, Type p)
splitForAllTyVar_maybe ty
  | ForAllTy (Bndr tv _) inner_ty <- coreFullView ty = Just (tv, inner_ty)
  | otherwise = Nothing

splitForAllForAllTyBinder_maybe
  :: HasPass p pass => Type p -> Maybe (ForAllBinder (TyVar p), Type p)
splitForAllForAllTyBinder_maybe ty
  | ForAllTy b inner_ty <- coreFullView ty = Just (b, inner_ty)
  | otherwise = Nothing

-- TODO: Rename 'splitForAllKiVar_maybe'
splitForAllForAllKiBinder_maybe
  :: HasPass p pass => Type p -> Maybe (KiVar p, Type p)
splitForAllForAllKiBinder_maybe ty
  | BigTyLamTy b inner_ty <- coreFullView ty = Just (b, inner_ty)
  | otherwise = Nothing

-- TODO: Rename
splitForAllForAllKiCoBinder_maybe
  :: HasPass p pass => Type p -> Maybe (KiCoVar p, Type p)
splitForAllForAllKiCoBinder_maybe ty
  | ForAllKiCo b inner_ty <- coreFullView ty = Just (b, inner_ty)
  | otherwise = Nothing

splitForAllInvisTyBinders :: HasPass p pass => Type p -> ([TyVar p], Type p)
splitForAllInvisTyBinders ty = split ty ty []
  where
    split _ (ForAllTy (Bndr tv Specified) ty) tvs = split ty ty (tv:tvs)
    split orig_ty ty tvs | Just ty' <- coreView ty = split orig_ty ty' tvs
    split orig_ty _ tvs = (reverse tvs, orig_ty)

splitForAllTyVars :: HasPass p pass => Type p -> ([TyVar p], Type p)
splitForAllTyVars ty = split ty ty []
  where
    split _ (ForAllTy (Bndr tv _) ty) tvs = split ty ty (tv:tvs)
    split orig_ty ty tvs | Just ty' <- coreView ty = split orig_ty ty' tvs
    split orig_ty _ tvs = (reverse tvs, orig_ty)

isForAllTy :: HasPass p pass => Type p -> Bool
isForAllTy ty
  | ForAllTy {} <- coreFullView ty = True
  | ForAllKiCo {} <- coreFullView ty = True
  | otherwise = False

isFunTy :: HasPass p pass => Type p -> Bool
isFunTy ty = case coreFullView ty of
  FunTy {} -> True
  _ -> False

isTauTy :: HasPass p pass => Type p -> Bool
isTauTy ty | Just ty' <- coreView ty = isTauTy ty'
isTauTy (TyVarTy _) = True
isTauTy (TyConApp tc tys) = all isTauTy tys && isTauTyCon tc
isTauTy (AppTy a b) = isTauTy a && isTauTy b
isTauTy (FunTy _ a b) = isTauTy a && isTauTy b
isTauTy (ForAllTy {}) = False
isTauTy (TyLamTy _ ty) = isTauTy ty
isTauTy other = pprPanic "isTauTy" (ppr other)

{-# INLINE splitPiTy_maybe #-} 
splitPiTy_maybe :: HasPass p pass => Type p -> Maybe (PiTyBinder p, Type p)
splitPiTy_maybe ty = case coreFullView ty of
  ForAllTy bndr ty -> Just (NamedTy bndr, ty)
  ForAllKiCo bndr ty -> Just (NamedKiCo bndr, ty)
  BigTyLamTy bndr ty -> Just (NamedKi bndr, ty)
  FunTy { ft_arg = arg, ft_res = res } -> Just (AnonTy arg, res)
  _ -> Nothing

splitPiTys :: HasPass p pass => Type p -> ([PiTyBinder p], Type p)
splitPiTys ty = split ty ty []
  where
    split _ (ForAllTy b res) bs = split res res (NamedTy b : bs)
    split _ (ForAllKiCo bndr res) bs = split res res (NamedKiCo bndr : bs)
    split _ (BigTyLamTy bndr res) bs = split res res (NamedKi bndr : bs)
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
  -> Kind Zk
  -> Arity
  -> Type Zk
  -> TyCon p
buildSynTyCon name kind arity rhs
  = mkSynonymTyCon name kind arity rhs is_tau is_forgetful is_concrete
  where
    is_tau = isTauTy rhs
    is_concrete = uniqSetAll isConcreteTyCon rhs_tycons
    is_forgetful = isForgetfulTy rhs

    rhs_tycons = tyConsOfType rhs

{- *********************************************************************
*                                                                      *
        Sequencing on types
*                                                                      *
********************************************************************* -}

seqType :: Type Zk -> ()
seqType (TyVarTy tv) = tv `seq` ()
seqType (AppTy t1 t2) = seqType t1 `seq` seqType t2
seqType (FunTy k t1 t2) = seqType t1 `seq` seqMonoKind k `seq` seqType t2
seqType (TyConApp tc tys) = tc `seq` seqTypes tys
seqType (ForAllTy (Bndr tv _) ty) = seqMonoKind (varKind tv) `seq` seqType ty
seqType (ForAllKiCo kcv ty) = seqMonoKind (varKind kcv) `seq` seqType ty
seqType (TyLamTy tv ty) = seqMonoKind (varKind tv) `seq` seqType ty
seqType (BigTyLamTy kv ty) = kv `seq` seqType ty
seqType (CastTy ty co) = seqType ty `seq` seqKiCo co
seqType (Embed ki) = seqMonoKind ki
seqType (KindCoercion co) = seqKiCo co

seqTypes :: [Type Zk] -> ()
seqTypes [] = ()
seqTypes (ty : tys) = seqType ty `seq` seqTypes tys

seqTyCo :: TypeCoercion Zk -> ()
seqTyCo (TyRefl ty) = seqType ty
seqTyCo (GRefl ty co) = seqType ty `seq` seqKiCo co
seqTyCo (TyConAppCo tc cos) = tc `seq` seqTyCos cos
seqTyCo (AppCo co1 co2) = seqTyCo co1 `seq` seqTyCo co2
seqTyCo (ForAllCo tv visL visR kco tco)
  = seqMonoKind (varKind tv) `seq` visL `seq` visR `seq` seqKiCo kco `seq` seqTyCo tco
seqTyCo (ForAllCoCo kcv kco tco)
  = seqMonoKind (varKind kcv) `seq` seqKiCo kco `seq` seqTyCo tco
seqTyCo (TyFunCo kco co1 co2) = seqKiCo kco `seq` seqTyCo co1 `seq` seqTyCo co2
seqTyCo (TyCoVarCo cv) = cv `seq` () 
seqTyCo (LiftKCo co) = seqKiCo co
seqTyCo (TySymCo co) = seqTyCo co 
seqTyCo (TyTransCo co1 co2) = seqTyCo co1 `seq` seqTyCo co2
seqTyCo (LRCo lr co) = lr `seq` seqTyCo co

seqTyCos :: [TypeCoercion Zk] -> ()
seqTyCos [] = ()
seqTyCos (co:cos) = seqTyCo co `seq` seqTyCos cos

{- *********************************************************************
*                                                                      *
        The kind of a type
*                                                                      *
********************************************************************* -}

typeKind :: (HasDebugCallStack, HasPass p pass)=> Type p -> Kind p
typeKind (BigTyLamTy kv res) = mkForAllKi kv (typeKind res)
typeKind (TyConApp tc []) = case tyConDetails tc of
  TcTyCon { tcTyConKind = ki } -> ki
  other -> fromZkKind $ tyConKind other
typeKind ty = Mono $ typeMonoKind ty

typeMonoKind :: (HasDebugCallStack, HasPass p pass) => Type p -> MonoKind p
typeMonoKind (TyConApp tc tys)
  = case tyConDetails tc of
      TcTyCon { tcTyConKind = ki } ->
        handle_non_mono (piKiResultTys ki tys)
        $ \ki -> vcat [ ppr tc <+> colon <+> ppr ki, ppr tys ]

      other ->
        handle_non_mono (piKiResultTys (fromZkKind $ tyConKind other) tys)
        $ \ki -> vcat [ ppr tc <+> colon <+> ppr ki, ppr tys ]
                        
typeMonoKind (FunTy { ft_kind = kind }) = kind
typeMonoKind (TyVarTy tyvar) = varKind tyvar
typeMonoKind (AppTy fun arg)
  = go fun [arg]
  where
    go (AppTy fun arg) args = go fun (arg:args)
    go fun args = handle_non_mono (piKiResultTys (typeKind fun) args)
                  $ \ki -> vcat [ ppr fun <+> colon <+> ppr ki
                                , ppr args ]
typeMonoKind ty@(ForAllTy {})
  = let (tvs, body) = splitForAllTyVars ty
        body_kind = typeMonoKind body
    in assertPpr (not (null tvs)) (ppr ty) body_kind
typeMonoKind ty@(ForAllKiCo {})
  = let (kcvs, body) = splitForAllKiCoVars ty
        body_kind = typeMonoKind body
    in assertPpr (not (null kcvs)) (ppr ty) body_kind
typeMonoKind ty@(TyLamTy tv res) =
  let tvKind = varKind tv
      res_kind = typeMonoKind res
      flag = chooseFunKiFlag tvKind res_kind
  in mkFunKi flag tvKind res_kind
typeMonoKind ty@(BigTyLamTy _ _) = pprPanic "typeMonoKind" (ppr ty)
typeMonoKind ty@(Embed _) = pprPanic "typeMonoKind" (ppr ty)
typeMonoKind (CastTy _ co) = kicoercionRKind co
typeMonoKind (KindCoercion kco) = kiCoercionKind kco
typeMonoKind (LocalTyRow _ ki) = ki
typeMonoKind (SetRowsTy base rows)
  = KiConApp $ KiCon Nothing (typeMonoKind base) (rowSigOfRow <$> rows)

rowSigOfRow :: HasPass p pass => SetRow p -> RowSig p
rowSigOfRow (SetRowVal nm) = RowTySig nm (panic "rowSigOfRow")
rowSigOfRow (SetRowTy nm ty) = RowKiSig nm (typeMonoKind ty)

handle_non_mono :: Kind p -> (Kind p -> SDoc) -> MonoKind p
handle_non_mono ki doc = case ki of
                           Mono ki -> ki
                           other -> pprPanic "typeMonoKind" (doc other)

{- **********************************************************************
*                                                                       *
            Simple constructors
*                                                                       *
********************************************************************** -}

mkTyVarTy :: TyVar p -> Type p
mkTyVarTy v = TyVarTy v

mkTyVarTys :: [TyVar p] -> [Type p]
mkTyVarTys = map mkTyVarTy

mkFunTys :: [Type p] -> [MonoKind p] -> Type p -> Type p
mkFunTys args fun_kis res_ty =
  assert (args `equalLength` fun_kis)
  $ foldr (uncurry mkFunTy) res_ty (zip fun_kis args)

mkForAllTy :: ForAllBinder (TyVar p) -> Type p -> Type p
mkForAllTy = ForAllTy

mkInfForAllTy :: TyVar p -> Type p -> Type p
mkInfForAllTy tv ty = ForAllTy (Bndr tv Inferred) ty

mkInfForAllTys :: [TyVar p] -> Type p -> Type p
mkInfForAllTys tvs ty = foldr mkInfForAllTy ty tvs

mkForAllKiCo :: KiCoVar p -> Type p -> Type p
mkForAllKiCo = ForAllKiCo

mkForAllTys :: [ForAllBinder (TyVar p)] -> Type p -> Type p
mkForAllTys tyvars ty = foldr ForAllTy ty tyvars

-- TODO: this is NOT like GHC (they use fun ty for kcos when the kcv does not occur in type)
-- This seems simpler for us without causing issues. Should double check anyways
mkForAllKiCos :: [KiCoVar p] -> Type p -> Type p
mkForAllKiCos bndrs ty = foldr ForAllKiCo ty bndrs

mkInvisForAllTys :: [InvisBinder (TyVar p)] -> Type p -> Type p
mkInvisForAllTys tyvars = mkForAllTys (varSpecToBinders tyvars)

mkFunTy :: HasDebugCallStack => MonoKind p -> Type p -> Type p -> Type p
mkFunTy = FunTy

tcMkFunTy :: MonoKind p -> Type p -> Type p -> Type p
tcMkFunTy = FunTy 

mkTyLamTy :: TyVar p -> Type p -> Type p
mkTyLamTy = TyLamTy

mkTyLamTys :: [TyVar p] -> Type p -> Type p
mkTyLamTys = flip (foldr mkTyLamTy)

mkBigLamTy :: KiVar p -> Type p -> Type p
mkBigLamTy = BigTyLamTy

mkBigLamTys :: [KiVar p] -> Type p -> Type p
mkBigLamTys = flip (foldr mkBigLamTy)

{- *********************************************************************
*                                                                      *
                    Space-saving construction
*                                                                      *
********************************************************************* -}

mkTyConAppCo
  :: (HasDebugCallStack, HasPass p pass)
  => TyCon p -> [TypeCoercion p] -> TypeCoercion p
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
  :: (HasDebugCallStack, HasPass p pass)
  => TyCon p -> [TypeCoercion p] -> Maybe (TypeCoercion p)
tyConAppFunCo_maybe tc cos
  | Just (LiftKCo arg_ki, LiftKCo res_ki, LiftKCo fun_ki, arg, res)
    <- ty_con_app_fun_maybe tc cos
  = Just (mkTyFunCo fun_ki arg res)
  | otherwise
  = Nothing

mkTyFunCo
  :: HasPass p pass
  => KindCoercion p
  -> TypeCoercion p
  -> TypeCoercion p
  -> TypeCoercion p
mkTyFunCo kco arg_co res_co
  | Just ty1 <- isReflTyCo_maybe arg_co
  , Just ty2 <- isReflTyCo_maybe res_co
  , Just k <- isReflKiCo_maybe kco
  = mkReflTyCo (mkFunTy k ty1 ty2)
  | otherwise
  = TyFunCo { tfco_ki = kco
            , tfco_arg = arg_co
            , tfco_res = res_co }

mkAppCo :: HasPass p pass => TypeCoercion p -> TypeCoercion p -> TypeCoercion p
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

mkAppCos :: HasPass p pass => TypeCoercion p -> [TypeCoercion p] -> TypeCoercion p
mkAppCos co1 cos = foldl' mkAppCo co1 cos

{- *********************************************************************
*                                                                      *
                    Type Coercions
*                                                                      *
********************************************************************* -}

liftKCo :: KindCoercion p -> TypeCoercion p
liftKCo = LiftKCo

mkTyCoVarCo :: TyCoVar p -> TypeCoercion p
mkTyCoVarCo = TyCoVarCo

mkTyHoleCo :: TypeCoercionHole -> TypeCoercion Tc
mkTyHoleCo = TyHoleCo

mkGReflRightCo :: Type p -> KindCoercion p -> TypeCoercion p 
mkGReflRightCo ty kco
  | isReflKiCo kco = mkReflTyCo ty
  | otherwise = mkGReflCo ty kco

mkGReflLeftCo :: Type p -> KindCoercion p -> TypeCoercion p
mkGReflLeftCo ty kco
  | isReflKiCo kco = mkReflTyCo ty
  | otherwise = mkSymTyCo $ mkGReflCo ty kco

ty_con_app_fun_maybe
  :: (HasDebugCallStack, Outputable a)
  => TyCon p
  -> [a]
  -> Maybe (a, a, a, a, a)
ty_con_app_fun_maybe tc args
  | tc_uniq == fUNTyConKey = fUN_case
  | otherwise = Nothing
  where
    tc_uniq = tyConUnique tc

    fUN_case
      | (arg_k : res_k : fun_k : arg : res : rest) <- args
      = assertPpr (null rest) (ppr tc <+> ppr args)
        $ Just (arg_k, res_k, fun_k, arg, res)
      | otherwise
      = Nothing
    
-- Given 'ty : k1', 'kco : k1 ~ k2', 'co : ty ~ ty2',
-- produces 'co' : (ty |> kco) ~ ty2'
mkCoherenceLeftCo :: Type p -> KindCoercion p -> TypeCoercion p -> TypeCoercion p
mkCoherenceLeftCo ty kco co
  | isReflKiCo kco = co
  | otherwise = (mkSymTyCo $ mkGReflCo ty kco) `mkTyTransCo` co

mkCoherenceRightCo :: Type p -> KindCoercion p -> TypeCoercion p -> TypeCoercion p
mkCoherenceRightCo ty kco co
  | isReflKiCo kco = co
  | otherwise = co `mkTyTransCo` mkGReflCo ty kco

mkGReflLeftMCo :: Type p -> Maybe (KindCoercion p) -> TypeCoercion p
mkGReflLeftMCo ty Nothing = mkReflTyCo ty
mkGReflLeftMCo ty (Just kco) = mkGReflLeftCo ty kco

mkGReflRightMCo :: Type p -> Maybe (KindCoercion p) -> TypeCoercion p
mkGReflRightMCo ty Nothing = mkReflTyCo ty
mkGReflRightMCo ty (Just kco) = mkGReflRightCo ty kco

mkCoherenceRightMCo
  :: Type p -> Maybe (KindCoercion p) -> TypeCoercion p -> TypeCoercion p
mkCoherenceRightMCo _ Nothing co2 = co2
mkCoherenceRightMCo ty (Just kco) co2 = mkCoherenceRightCo ty kco co2

tyCoHoleCoVar :: TypeCoercionHole -> TcTyCoVar 
tyCoHoleCoVar = tch_co_var

mkGReflCo :: Type p -> KindCoercion p -> TypeCoercion p
mkGReflCo ty kco
  | isReflKiCo kco = TyRefl ty
  | otherwise = GRefl ty kco

mkSymTyCo :: TypeCoercion p -> TypeCoercion p
mkSymTyCo co | isReflTyCo co = co
mkSymTyCo (TySymCo co) = co
mkSymTyCo (LiftKCo kco) = LiftKCo $ mkSymKiCo kco
mkSymTyCo co = TySymCo co

mkTyTransCo :: TypeCoercion p -> TypeCoercion p -> TypeCoercion p
mkTyTransCo co1 co2
  | LiftKCo kco1 <- co1
  = case co2 of
      LiftKCo kco2 -> LiftKCo $ mkTransKiCo kco1 kco2
      _ -> pprPanic "mkTyTransCo" (ppr co1 $$ ppr co2)
  | LiftKCo _ <- co2
  = pprPanic "mkTyTransCo" (ppr co1 $$ ppr co2)
  | isReflTyCo co1 = co2
  | isReflTyCo co2 = co1
  | GRefl t1 kco1 <- co1
  , GRefl t2 kco2 <- co2
  = GRefl t1 (mkTransKiCo kco1 kco2)
  | otherwise
  = TyTransCo co1 co2

mkTyEqPred :: HasPass p pass => Type p -> Type p -> Type p
mkTyEqPred ty1 ty2
  = mkTyConApp eqTyCon [Embed ki1, Embed ki2, ty1, ty2]
  where
    ki1 = typeMonoKind ty1
    ki2 = typeMonoKind ty2

decomposeFunCo
  :: (HasDebugCallStack, HasPass p pass)
  => KindCoercion p
  -> (KindCoercion p, KindCoercion p)
decomposeFunCo (FunCo { fco_arg = co1, fco_res = co2 })
  = (co1, co2)
decomposeFunCo co
  = assertPpr all_ok (ppr co)
    $ (mkSelCo (SelFun SelArg) co, mkSelCo (SelFun SelRes) co)
  where
    (_, Pair k1 k2) = kiCoercionParts co
    all_ok = isMonoFunKi k1 && isMonoFunKi k2

decomposePiCos
  :: (HasDebugCallStack, HasPass p pass)
  => KindCoercion p -> (KiPredCon, Pair (MonoKind p))
  -> [Type p] -- unused (or used only for its length)
  -> ([KindCoercion p], KindCoercion p)
decomposePiCos orig_kco (EQKi, (Pair orig_ki1 orig_ki2)) orig_args
  = go [] orig_ki1 orig_kco orig_ki2 orig_args
  where
    go acc_arg_cos k1 co k2 (_:tys)
      | Just (af1, _, r1) <- splitMonoFunKi_maybe k1
      , Just (af2, _, r2) <- splitMonoFunKi_maybe k2
      , af1 == af2
      = let (sym_arg_co, res_co) = decomposeFunCo co
            arg_co = mkSymKiCo sym_arg_co
        in go (arg_co : acc_arg_cos) r1 res_co r2 tys

    go acc_arg_cos _ co _ _ = (reverse acc_arg_cos, co)
decomposePiCos co stuff args = pprPanic "decomposePiCos not EQKi"
                               $ vcat [ ppr co, ppr stuff, ppr args ]

setCoHoleType :: TypeCoercionHole -> Type Tc -> TypeCoercionHole
setCoHoleType h t = setTyCoHoleCoVar h (setVarType (tyCoHoleCoVar h) t)

setTyCoHoleCoVar :: TypeCoercionHole -> TcTyCoVar -> TypeCoercionHole
setTyCoHoleCoVar h cv = h { tch_co_var = cv }

castCoercionKind2
  :: TypeCoercion p
  -> Type p -> Type p
  -> KindCoercion p -> KindCoercion p
  -> TypeCoercion p
castCoercionKind2 g t1 t2 h1 h2
  = mkCoherenceRightCo t2 h2 (mkCoherenceLeftCo t1 h1 g)

castCoercionKind1
  :: HasPass p pass => TypeCoercion p -> Type p -> Type p -> KindCoercion p -> TypeCoercion p
castCoercionKind1 g t1 t2 h
  = case g of
      TyRefl {} -> mkReflTyCo (mkCastTy t2 h)
      GRefl _ kco -> mkGReflCo (mkCastTy t1 h) (mkSymKiCo h `mkTransKiCo` kco `mkTransKiCo` h)
      _ -> castCoercionKind2 g t1 t2 h h

{- *********************************************************************
*                                                                      *
              MCoercion
*                                                                      *
********************************************************************* -}

mkSymMCo :: MTypeCoercion p -> MTypeCoercion p
mkSymMCo MRefl = MRefl
mkSymMCo (MCo co) = MCo (mkSymTyCo co)

mkPiMCos :: [a] -> MTypeCoercion p -> MTypeCoercion p
mkPiMCos _ MRefl = MRefl
mkPiMCos _ _ = panic "mkPiMCos"

mkFunResMCo :: a -> MTypeCoercion p -> MTypeCoercion p
mkFunResMCo _ MRefl = MRefl
mkFunResMCo _ _ = panic "mkFunResMCo"

{- *********************************************************************
*                                                                      *
              Sum/Tuple
*                                                                      *
********************************************************************* -}

isTupleType :: Type Zk -> Bool
isTupleType ty
  | Just tc <- tyConAppTyCon_maybe ty
  = isTupleTyCon tc
  | otherwise
  = False

isSumType :: Type Zk -> Bool
isSumType ty
  | Just tc <- tyConAppTyCon_maybe ty
  = isSumTyCon tc
  | otherwise
  = False

{- *********************************************************************
*                                                                      *
              Join points
*                                                                      *
********************************************************************* -}

-- See GHC [The polymorphism rule of join points]
isValidJoinPointType :: JoinArity -> Type Zk -> Bool
isValidJoinPointType arity ty
  = valid_under (emptyVarSet, emptyVarSet, emptyVarSet) arity ty
  where
    valid_under
      :: (VarSet (TyVar Zk), VarSet (KiCoVar Zk), VarSet (KiVar Zk))
      -> JoinArity
      -> Type Zk
      -> Bool
    valid_under (tvs, kcvs, kvs) arity ty
      | arity == 0
      = let (tvs1, kcvs1, kvs1) = varsOfType ty
        in tvs `disjointVarSet` tvs1 &&
           kcvs `disjointVarSet` kcvs1 &&
           kvs `disjointVarSet` kvs1
      | Just (k, ty') <- splitForAllForAllKiBinder_maybe ty
      = valid_under (tvs, kcvs, kvs `extendVarSet` k) (arity - 1) ty'
      | Just (c, ty') <- splitForAllForAllKiCoBinder_maybe ty
      = valid_under (tvs, kcvs `extendVarSet` c, kvs) (arity - 1) ty'
      | Just (t, ty') <- splitForAllTyVar_maybe ty
      = valid_under (tvs `extendVarSet` t, kcvs, kvs) (arity - 1) ty'
      | Just (_, _, res_ty) <- splitFunTy_maybe ty
      = valid_under (tvs, kcvs, kvs) (arity - 1) res_ty
      | otherwise
      = False

{- *********************************************************************
*                                                                      *
                   typeSize
*                                                                      *
********************************************************************* -}

typeSize :: HasPass p pass => Type p -> Int
typeSize (TyVarTy {}) = 1
typeSize (AppTy t1 t2) = typeSize t1 + typeSize t2
typeSize (TyLamTy _ t) = 1 + typeSize t
typeSize (BigTyLamTy _ t) = 1 + typeSize t
typeSize (TyConApp _ ts) = 1 + typesSize ts
typeSize (ForAllTy (Bndr tv _) t) = panic "kindSize (varKind tv) + typeSize t"
typeSize (ForAllKiCo kcv t) = panic "typeSize ForAllKiCo"
typeSize (FunTy _ t1 t2) = typeSize t1 + typeSize t2
typeSize (Embed _) = 1
typeSize (CastTy ty _) = typeSize ty
typeSize co@(KindCoercion _) = pprPanic "typeSize" (ppr co)

typesSize :: HasPass p pass => [Type p] -> Int
typesSize tys = foldr ((+) . typeSize) 0 tys
