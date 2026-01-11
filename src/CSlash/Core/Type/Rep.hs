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
import Data.IORef (IORef)
import Control.DeepSeq

{- **********************************************************************
*                                                                       *
                        Type
*                                                                       *
********************************************************************** -}

data Type tv kv
  = TyVarTy tv
  | AppTy (Type tv kv) (Type tv kv) -- The first arg must be an 'AppTy' or a 'TyVarTy' or a 'TyLam'
  | TyLamTy tv (Type tv kv) -- Used for TySyns, NOT in the types of DataCons (only Foralls)
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

type PredType = Type

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
            Type Coercions
*                                                                       *
********************************************************************** -}

data TypeCoercion tv kv
  = TyRefl (Type tv kv)
  | GRefl (Type tv kv) (KindCoercion kv)
  | TyConAppCo (TyCon tv kv) [TypeCoercion tv kv]
  | AppCo (TypeCoercion tv kv) (TypeCoercion tv kv)
  | TyFunCo
    { tfco_ki :: (KindCoercion kv)
    , tfco_arg :: (TypeCoercion tv kv)
    , tfco_res :: (TypeCoercion tv kv)
    }
  | TyCoVarCo (TyCoVar tv kv)
  | LiftKCo (KindCoercion kv)
  | TySymCo (TypeCoercion tv kv)
  | TyTransCo (TypeCoercion tv kv) (TypeCoercion tv kv)
  | LRCo LeftOrRight (TypeCoercion tv kv)
  | TyHoleCo (TypeCoercionHole tv kv)
  deriving Data.Data

data TypeCoercionHole tv kv = TypeCoercionHole
  { tch_co_var :: TyCoVar tv kv
  , tch_ref :: IORef (Maybe (TypeCoercion (AnyTyVar AnyKiVar) AnyKiVar))
  }

instance (Data.Typeable tv, Data.Typeable kv) => Data.Data (TypeCoercionHole tv kv)

instance Outputable (TypeCoercion tv kv) where
  ppr = const $ text "[TyCo]"

instance Outputable (TypeCoercionHole tv kv) where
  ppr = const $ text "[TyCoHole]"

instance Uniquable (TypeCoercionHole tv kv) where
  getUnique (TypeCoercionHole { tch_co_var = cv }) = getUnique cv

liftKCo :: KindCoercion kv -> TypeCoercion tv kv
liftKCo = LiftKCo

mkReflTyCo :: Type tv kv -> TypeCoercion tv kv
mkReflTyCo (Embed ki) = LiftKCo (mkReflKiCo ki)
mkReflTyCo ty = TyRefl ty

mkTyCoVarCo :: TyCoVar tv kv -> TypeCoercion tv kv
mkTyCoVarCo = TyCoVarCo

mkTyHoleCo :: TypeCoercionHole tv kv -> TypeCoercion tv kv
mkTyHoleCo = TyHoleCo

mkGReflCo :: Type tv kv -> KindCoercion kv -> TypeCoercion tv kv
mkGReflCo ty kco
  | isReflKiCo kco = TyRefl ty
  | otherwise = GRefl ty kco

mkGReflRightCo :: Type tv kv -> KindCoercion kv -> TypeCoercion tv kv 
mkGReflRightCo ty kco
  | isReflKiCo kco = mkReflTyCo ty
  | otherwise = mkGReflCo ty kco

mkGReflLeftCo :: Type tv kv -> KindCoercion kv -> TypeCoercion tv kv
mkGReflLeftCo ty kco
  | isReflKiCo kco = mkReflTyCo ty
  | otherwise = mkSymTyCo $ mkGReflCo ty kco

ty_con_app_fun_maybe
  :: (HasDebugCallStack, Outputable a)
  => TyCon tv kv
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
    
mkSymTyCo :: TypeCoercion tv kv -> TypeCoercion tv kv
mkSymTyCo co | isReflTyCo co = co
mkSymTyCo (TySymCo co) = co
mkSymTyCo (LiftKCo kco) = LiftKCo $ mkSymKiCo kco
mkSymTyCo co = TySymCo co

mkTyTransCo :: TypeCoercion tv kv -> TypeCoercion tv kv -> TypeCoercion tv kv
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

-- Given 'ty : k1', 'kco : k1 ~ k2', 'co : ty ~ ty2',
-- produces 'co' : (ty |> kco) ~ ty2'
mkCoherenceLeftCo :: Type tv kv -> KindCoercion kv -> TypeCoercion tv kv -> TypeCoercion tv kv
mkCoherenceLeftCo ty kco co
  | isReflKiCo kco = co
  | otherwise = (mkSymTyCo $ mkGReflCo ty kco) `mkTyTransCo` co

mkCoherenceRightCo :: Type tv kv -> KindCoercion kv -> TypeCoercion tv kv -> TypeCoercion tv kv
mkCoherenceRightCo ty kco co
  | isReflKiCo kco = co
  | otherwise = co `mkTyTransCo` mkGReflCo ty kco

mkGReflLeftMCo :: Type tv kv -> Maybe (KindCoercion kv) -> TypeCoercion tv kv
mkGReflLeftMCo ty Nothing = mkReflTyCo ty
mkGReflLeftMCo ty (Just kco) = mkGReflLeftCo ty kco

mkGReflRightMCo :: Type tv kv -> Maybe (KindCoercion kv) -> TypeCoercion tv kv
mkGReflRightMCo ty Nothing = mkReflTyCo ty
mkGReflRightMCo ty (Just kco) = mkGReflRightCo ty kco

mkCoherenceRightMCo
  :: Type tv kv -> Maybe (KindCoercion kv) -> TypeCoercion tv kv -> TypeCoercion tv kv
mkCoherenceRightMCo _ Nothing co2 = co2
mkCoherenceRightMCo ty (Just kco) co2 = mkCoherenceRightCo ty kco co2

tyCoHoleCoVar :: TypeCoercionHole tv kv -> TyCoVar tv kv
tyCoHoleCoVar = tch_co_var

isReflTyCo :: TypeCoercion tv kv -> Bool
isReflTyCo (TyRefl {}) = True
isReflTyCo (GRefl _ kco) = isReflKiCo kco
isReflTyCo (LiftKCo kco) = isReflKiCo kco
isReflTyCo _ = False

isReflTyCo_maybe :: IsTyVar tv kv => TypeCoercion tv kv -> Maybe (Type tv kv)
isReflTyCo_maybe (TyRefl ty) = Just ty
isReflTyCo_maybe (GRefl ty kco)
  | isReflKiCo kco = pprPanic "isReflTyCo_maybe/GRefl" (ppr ty <+> text "|>" <+> ppr kco)
isReflTyCo_maybe (LiftKCo kco)
  | Just ki <- isReflKiCo_maybe kco
  = Just (Embed ki)
isReflTyCo_maybe _ = Nothing

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

mkFunTys :: [Type tv kv] -> [MonoKind kv] -> Type tv kv -> Type tv kv
mkFunTys args fun_kis res_ty =
  assert (args `equalLength` fun_kis)
  $ foldr (uncurry mkFunTy) res_ty (zip fun_kis args)

mkForAllTys :: [ForAllBinder tv] -> Type tv kv -> Type tv kv
mkForAllTys tyvars ty = foldr ForAllTy ty tyvars

mkInvisForAllTys :: [InvisBinder tv] -> Type tv kv -> Type tv kv
mkInvisForAllTys tyvars = mkForAllTys (varSpecToBinders tyvars)

mkFunTy :: HasDebugCallStack => MonoKind kv -> Type tv kv -> Type tv kv -> Type tv kv
mkFunTy = FunTy

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

data TyCoFolder tv kv env env' b a  = TyCoFolder
  { tcf_view :: Type tv kv -> Maybe (Type tv kv)
  , tcf_tyvar :: env -> tv -> a
  , tcf_covar :: env -> TyCoVar tv kv -> a
  , tcf_hole :: env -> TypeCoercionHole tv kv -> a
  , tcf_tybinder :: env -> tv -> ForAllFlag -> env
  , tcf_tylambinder :: env -> tv -> env
  , tcf_tylamkibinder :: env -> kv -> env
  , tcf_swapEnv :: env -> env'
  , tcf_embedKiRes :: b -> a
  , tcf_mkcf :: MKiCoFolder kv env' b
  }

{-# INLINE foldTyCo #-}
foldTyCo
  :: (Monoid a, Monoid b, Outputable tv, Outputable kv, VarHasKind tv kv)
  => TyCoFolder tv kv env env' b a
  -> env
  -> ( Type tv kv -> a, [Type tv kv] -> a
     , TypeCoercion tv kv -> a, [TypeCoercion tv kv] -> a )
foldTyCo (TyCoFolder { tcf_view = view
                     , tcf_tyvar = tyvar
                     , tcf_covar = covar
                     , tcf_hole = cohole
                     , tcf_tybinder = tybinder
                     , tcf_tylambinder = tylambinder
                     , tcf_tylamkibinder = tylamkibinder
                     , tcf_swapEnv = tokenv
                     , tcf_embedKiRes = embedRes
                     , tcf_mkcf = mkcf }) env
  = (go_ty env, go_tys env, go_co env, go_cos env)
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

    go_cos _ [] = mempty
    go_cos env (c:cs) = go_co env c `mappend` go_cos env cs

    go_co env (TyRefl ty) = go_ty env ty
    go_co env (GRefl ty kco) = go_ty env ty `mappend` embedRes (go_kco kco)
      where go_kco = case foldMonoKiCo mkcf (tokenv env) of
                       (_, _, f, _) -> f
    go_co env (TyConAppCo _ cos) = go_cos env cos
    go_co env (AppCo c1 c2) = go_co env c1 `mappend` go_co env c2
    go_co env (TyCoVarCo cv) = covar env cv
    go_co env (TyHoleCo hole) = cohole env hole
    go_co env (TySymCo co) = go_co env co
    go_co env (TyTransCo c1 c2) = go_co env c1 `mappend` go_co env c2
    go_co env (LRCo _ co) = go_co env co
    go_co env (LiftKCo kco) = embedRes $ go_kco kco
      where go_kco = case foldMonoKiCo mkcf (tokenv env) of
                       (_, _, f, _) -> f
    go_co env (TyFunCo kco c1 c2)
      = embedRes (go_kco kco) `mappend` go_co env c1 `mappend` go_co env c2
      where go_kco = case foldMonoKiCo mkcf (tokenv env) of
                       (_, _, f, _) -> f

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
