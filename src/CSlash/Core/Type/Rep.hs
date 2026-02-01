{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Core.Type.Rep where

import {-# SOURCE #-} CSlash.Core.Type.Ppr (pprType)

import CSlash.Cs.Pass

import CSlash.Types.Var.TyVar
import CSlash.Types.Var.KiVar
import CSlash.Types.Var.CoVar
import CSlash.Types.Var.Class
import CSlash.Types.Var.Set
import CSlash.Core.TyCon
import CSlash.Core.Kind
import CSlash.Core.Kind.Compare

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

data Type p
  = TyVarTy (TyVar p)
  | AppTy (Type p) (Type p) -- The first arg must be an 'AppTy' or a 'TyVarTy' or a 'TyLam'
  | TyLamTy (TyVar p) (Type p) -- Used for TySyns, NOT in the types of DataCons (only Foralls)
  | BigTyLamTy (KiVar p) (Type p)
  | TyConApp (TyCon p) [Type p]
  | ForAllTy {-# UNPACK #-} !(ForAllBinder (TyVar p)) (Type p)
  | ForAllKiCo {-# UNPACK #-} !(KiCoVar p) (Type p)
  | FunTy
    { ft_kind :: MonoKind p
    , ft_arg :: Type p
    , ft_res :: Type p
    }
  | CastTy (Type p) (KindCoercion p)
  | Embed (MonoKind p) -- for application to a 'BigTyLamTy
  | KindCoercion (KindCoercion p) -- embed a kind coercion (evidence stuff)
  deriving Data.Data

type PredType = Type

instance Outputable (Type p) where
  ppr = pprType

type KnotTied ty = ty

{- **********************************************************************
*                                                                       *
            Type Coercions
*                                                                       *
********************************************************************** -}

data TypeCoercion p where
  TyRefl :: Type p -> TypeCoercion p
  GRefl :: Type p -> KindCoercion p -> TypeCoercion p
  TyConAppCo :: TyCon p -> [TypeCoercion p] -> TypeCoercion p
  AppCo :: TypeCoercion p -> TypeCoercion p -> TypeCoercion p
  ForAllCo
    :: { tfco_tv :: TyVar p
       , tfco_visL :: !ForAllFlag
       , tfco_visR :: !ForAllFlag
       , tfco_tv_kind_co :: KindCoercion p
       , tfco_body :: TypeCoercion p }
    -> TypeCoercion p
  ForAllCoCo
    :: { tfcoco_kcv :: KiCoVar p
       , tfcoco_kcv_kind_co :: KindCoercion p
       , tfcoco_body :: TypeCoercion p }
    -> TypeCoercion p
  TyFunCo
    :: { tfco_ki :: KindCoercion p
       , tfco_arg :: TypeCoercion p
       , tfco_res :: TypeCoercion p
       }
    -> TypeCoercion p
  TyCoVarCo :: TyCoVar p -> TypeCoercion p
  LiftKCo :: KindCoercion p -> TypeCoercion p
  TySymCo :: TypeCoercion p -> TypeCoercion p
  TyTransCo :: TypeCoercion p -> TypeCoercion p -> TypeCoercion p
  LRCo :: LeftOrRight -> TypeCoercion p -> TypeCoercion p
  TyHoleCo :: TypeCoercionHole -> TypeCoercion Tc

instance Data.Typeable p => Data.Data (TypeCoercion p)

data TypeCoercionHole = TypeCoercionHole
  { tch_co_var :: TyCoVar Tc
  , tch_ref :: IORef (Maybe (TypeCoercion Tc))
  }

instance Data.Data TypeCoercionHole

instance Outputable (TypeCoercion p) where
  ppr = const $ text "[TyCo]"

instance Outputable TypeCoercionHole where
  ppr = const $ text "[TyCoHole]"

instance Uniquable TypeCoercionHole where
  getUnique (TypeCoercionHole { tch_co_var = cv }) = getUnique cv

liftKCo :: KindCoercion p -> TypeCoercion p
liftKCo = LiftKCo

mkReflTyCo :: Type p -> TypeCoercion p
mkReflTyCo (Embed ki) = LiftKCo (mkReflKiCo ki)
mkReflTyCo ty = TyRefl ty

mkTyCoVarCo :: TyCoVar p -> TypeCoercion p
mkTyCoVarCo = TyCoVarCo

mkTyHoleCo :: TypeCoercionHole -> TypeCoercion Tc
mkTyHoleCo = TyHoleCo

mkGReflCo :: Type p -> KindCoercion p -> TypeCoercion p
mkGReflCo ty kco
  | isReflKiCo kco = TyRefl ty
  | otherwise = GRefl ty kco

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

tyCoHoleCoVar :: TypeCoercionHole -> TyCoVar Tc
tyCoHoleCoVar = tch_co_var

isReflTyCo :: TypeCoercion p -> Bool
isReflTyCo (TyRefl {}) = True
isReflTyCo (GRefl _ kco) = isReflKiCo kco
isReflTyCo (LiftKCo kco) = isReflKiCo kco
isReflTyCo _ = False

isReflTyCo_maybe :: TypeCoercion p -> Maybe (Type p)
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

data E3 a b c = In1 a | In2 b | In3 c

instance HasFVs (Type p) where
  type FVInScope (Type p) = (TyVarSet p, KiCoVarSet p, KiVarSet p)
  type FVAcc (Type p) = ([TyVar p], TyVarSet p, [KiCoVar p], KiCoVarSet p, [KiVar p], KiVarSet p)
  type FVArg (Type p) = E3 (TyVar p) (KiCoVar p) (KiVar p)

  fvElemAcc (In1 tv) (_, haveSet, _, _, _, _) = tv `elemVarSet` haveSet
  fvElemAcc (In2 kcv) (_, _, _, haveSet, _, _) = kcv `elemVarSet` haveSet
  fvElemAcc (In3 kv) (_, _, _, _, _, haveSet) = kv `elemVarSet` haveSet

  fvElemIS (In1 tv) (in_scope, _, _) = tv `elemVarSet` in_scope
  fvElemIS (In2 kcv) (_, in_scope, _) = kcv `elemVarSet` in_scope
  fvElemIS (In3 kv) (_, _, in_scope) = kv `elemVarSet` in_scope

  fvExtendAcc (In1 tv) (have, haveSet, kcs, kcset, ks, kset)
    = (tv:have, extendVarSet haveSet tv, kcs, kcset, ks, kset)
  fvExtendAcc (In2 kcv) (ts, tset, have, haveSet, ks, kset)
    = (ts, tset, kcv:have, extendVarSet haveSet kcv, ks, kset)
  fvExtendAcc (In3 kv) (ts, tset, kcs, kcset, have, haveSet)
    = (ts, tset, kcs, kcset, kv:have, extendVarSet haveSet kv)

  fvExtendIS (In1 tv) (in_scope, kcs, ks) = (extendVarSet in_scope tv, kcs, ks)
  fvExtendIS (In2 kcv) (ts, in_scope, ks) = (ts, extendVarSet in_scope kcv, ks)
  fvExtendIS (In3 kv) (ts, kcs, in_scope) = (ts, kcs, extendVarSet in_scope kv)

  fvEmptyAcc = ([], emptyVarSet, [], emptyVarSet, [], emptyVarSet)
  fvEmptyIS = (emptyVarSet, emptyVarSet, emptyVarSet)

{- **********************************************************************
*                                                                       *
            Simple constructors
*                                                                       *
********************************************************************** -}

mkTyVarTy :: TyVar p -> Type p
mkTyVarTy v = TyVarTy v

mkTyVarTys :: [TyVar p] -> [Type p]
mkTyVarTys = map mkTyVarTy

mkNakedTyConTy :: TyCon p -> Type p
mkNakedTyConTy tycon = TyConApp tycon []

mkFunTys :: [Type p] -> [MonoKind p] -> Type p -> Type p
mkFunTys args fun_kis res_ty =
  assert (args `equalLength` fun_kis)
  $ foldr (uncurry mkFunTy) res_ty (zip fun_kis args)

mkForAllTy :: TyVar p -> ForAllFlag -> Type p -> Type p
mkForAllTy tv vis ty = ForAllTy (Bndr tv vis) ty

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
                foldType
*                                                                      *
********************************************************************* -}

data TyCoFolder p env env' b a  = TyCoFolder
  { tcf_view :: Type p -> Maybe (Type p)
  , tcf_tyvar :: env -> TyVar p -> a
  , tcf_covar :: env -> TyCoVar p -> a
  , tcf_hole :: env -> TypeCoercionHole -> a
  , tcf_tybinder :: env -> TyVar p -> ForAllFlag -> env
  , tcf_kcobinder :: env -> KiCoVar p -> env
  , tcf_tylambinder :: env -> TyVar p -> env
  , tcf_tylamkibinder :: env -> KiVar p -> env
  , tcf_swapEnv :: env -> env'
  , tcf_embedKiRes :: b -> a
  , tcf_mkcf :: MKiCoFolder p env' b
  }

{-# INLINE foldTyCo #-}
foldTyCo
  :: (Monoid a, Monoid b)
  => TyCoFolder p env env' b a
  -> env
  -> ( Type p -> a, [Type p] -> a
     , TypeCoercion p -> a, [TypeCoercion p] -> a )
foldTyCo (TyCoFolder { tcf_view = view
                     , tcf_tyvar = tyvar
                     , tcf_covar = covar
                     , tcf_hole = cohole
                     , tcf_tybinder = tybinder
                     , tcf_kcobinder = kcobinder
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
    go_ty env (ForAllKiCo kcv inner)
      = let !env' = kcobinder env kcv
        in embedRes (go_mki (varKind kcv)) `mappend` go_ty env' inner
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
    go_co env (ForAllCo tv _ _ kco co)
      = embedRes (go_kco kco)
        `mappend` embedRes (go_mki (varKind tv))
        `mappend` go_co env' co
      where
        env' = tybinder env tv Inferred
        (go_mki, go_kco) = case foldMonoKiCo mkcf (tokenv env) of
                             (f1, _, f2, _) -> (f1, f2)
    go_co env (ForAllCoCo kcv kco co)
      = embedRes (go_kco kco)
        `mappend` embedRes (go_mki (varKind kcv))
        `mappend` go_co env' co
      where
        env' = kcobinder env kcv
        (go_mki, go_kco) = case foldMonoKiCo mkcf (tokenv env) of
                             (f1, _, f2, _) -> (f1, f2)

noView :: Type p -> Maybe (Type p)
noView _ = Nothing

{- *********************************************************************
*                                                                      *
                   typeSize
*                                                                      *
********************************************************************* -}

typeSize :: Type p -> Int
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

typesSize :: [Type p] -> Int
typesSize tys = foldr ((+) . typeSize) 0 tys
