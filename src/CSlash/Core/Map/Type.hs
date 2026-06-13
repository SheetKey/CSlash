{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Map.Type where

import CSlash.Cs.Pass

import CSlash.Core as C
import CSlash.Core.Type hiding (tm_tycon)
import CSlash.Core.Type.Rep
import CSlash.Core.Kind
import CSlash.Core.TyCon( isForgetfulSynTyCon )
import CSlash.Data.TrieMap

import CSlash.Data.FastString
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Unique
import CSlash.Types.Unique.FM
import CSlash.Utils.Outputable

import CSlash.Utils.Panic

import qualified Data.Map    as Map
import qualified Data.IntMap as IntMap

import Control.Monad ( (>=>) )

{-# SPECIALIZE lkG :: Key TypeMapX     -> TypeMapG a     -> Maybe a #-}
{-# SPECIALIZE lkG :: Key MonoKindMapX     -> MonoKindMapG a     -> Maybe a #-}
{-# SPECIALIZE lkG :: Key TypeCoercionMapX -> TypeCoercionMapG a -> Maybe a #-}
{-# SPECIALIZE lkG :: Key KindCoercionMapX -> KindCoercionMapG a -> Maybe a #-}

{-# SPECIALIZE xtG :: Key TypeMapX     -> XT a -> TypeMapG a -> TypeMapG a #-}
{-# SPECIALIZE xtG :: Key MonoKindMapX     -> XT a -> MonoKindMapG a -> MonoKindMapG a #-}
{-# SPECIALIZE xtG :: Key TypeCoercionMapX -> XT a -> TypeCoercionMapG a -> TypeCoercionMapG a #-}
{-# SPECIALIZE xtG :: Key KindCoercionMapX -> XT a -> KindCoercionMapG a -> KindCoercionMapG a #-}

{-# SPECIALIZE mapG :: (a -> b) -> TypeMapG a     -> TypeMapG b #-}
{-# SPECIALIZE mapG :: (a -> b) -> MonoKindMapG a     -> MonoKindMapG b #-}
{-# SPECIALIZE mapG :: (a -> b) -> TypeCoercionMapG a -> TypeCoercionMapG b #-}
{-# SPECIALIZE mapG :: (a -> b) -> TypeCoercionMapG a -> TypeCoercionMapG b #-}

{-# SPECIALIZE fdG :: (a -> b -> b) -> TypeMapG a     -> b -> b #-}
{-# SPECIALIZE fdG :: (a -> b -> b) -> MonoKindMapG a     -> b -> b #-}
{-# SPECIALIZE fdG :: (a -> b -> b) -> TypeCoercionMapG a -> b -> b #-}
{-# SPECIALIZE fdG :: (a -> b -> b) -> KindCoercionMapG a -> b -> b #-}

{- *********************************************************************
*                                                                      *
                   Coercions
*                                                                      *
********************************************************************* -}

newtype TypeCoercionMap a = TypeCoercionMap (TypeCoercionMapG a)

instance Functor TypeCoercionMap where
  fmap f = \(TypeCoercionMap m) -> TypeCoercionMap (fmap f m)
  {-# INLINE fmap #-}

instance TrieMap TypeCoercionMap where
  type Key TypeCoercionMap = CoreTypeCoercion
  emptyTM = TypeCoercionMap emptyTM
  lookupTM k (TypeCoercionMap m) = lookupTM (deBruijnize k) m
  alterTM k f (TypeCoercionMap m) = TypeCoercionMap (alterTM (deBruijnize k) f m)
  foldTM k (TypeCoercionMap m) = foldTM k m
  filterTM f (TypeCoercionMap m) = TypeCoercionMap (filterTM f m)

type TypeCoercionMapG = GenMap TypeCoercionMapX
newtype TypeCoercionMapX a = TypeCoercionMapX (TypeMapX a)

instance Functor TypeCoercionMapX where
  fmap f = \(TypeCoercionMapX core_tm) -> TypeCoercionMapX (fmap f core_tm)
  {-# INLINE fmap #-}

instance TrieMap TypeCoercionMapX where
  type Key TypeCoercionMapX = DeBruijn CoreTypeCoercion
  emptyTM = TypeCoercionMapX emptyTM
  lookupTM = lkTC
  alterTM = xtTC
  foldTM f (TypeCoercionMapX core_tm) = foldTM f core_tm
  filterTM f (TypeCoercionMapX core_tm) = TypeCoercionMapX (filterTM f core_tm)

instance Eq (DeBruijn (TypeCoercion Zk)) where
  D env1 co1 == D env2 co2
    = D env1 (tycoercionType co1) == D env2 (tycoercionType co2)

lkTC :: DeBruijn CoreTypeCoercion -> TypeCoercionMapX a -> Maybe a
lkTC (D env co) (TypeCoercionMapX core_tm) = lkT (D env $ tycoercionType co) core_tm

xtTC :: DeBruijn CoreTypeCoercion -> XT a -> TypeCoercionMapX a -> TypeCoercionMapX a
xtTC (D env co) f (TypeCoercionMapX m)
  = TypeCoercionMapX (xtT (D env $ tycoercionType co) f m)

newtype KindCoercionMap a = KindCoercionMap (KindCoercionMapG a)

instance Functor KindCoercionMap where
  fmap f = \(KindCoercionMap m) -> KindCoercionMap (fmap f m)
  {-# INLINE fmap #-}

instance TrieMap KindCoercionMap where
  type Key KindCoercionMap = CoreKindCoercion
  emptyTM = KindCoercionMap emptyTM
  lookupTM k (KindCoercionMap m) = lookupTM (deBruijnize k) m
  alterTM k f (KindCoercionMap m) = KindCoercionMap (alterTM (deBruijnize k) f m)
  foldTM k (KindCoercionMap m) = foldTM k m
  filterTM f (KindCoercionMap m) = KindCoercionMap (filterTM f m)

type KindCoercionMapG = GenMap KindCoercionMapX
newtype KindCoercionMapX a = KindCoercionMapX (MonoKindMapX a)

instance Functor KindCoercionMapX where
  fmap f = \(KindCoercionMapX core_km) -> KindCoercionMapX (fmap f core_km)
  {-# INLINE fmap #-}

instance TrieMap KindCoercionMapX where
  type Key KindCoercionMapX = DeBruijn CoreKindCoercion
  emptyTM = KindCoercionMapX emptyTM
  lookupTM = lkKC
  alterTM = xtKC
  foldTM f (KindCoercionMapX core_km) = foldTM f core_km
  filterTM f (KindCoercionMapX core_km) = KindCoercionMapX (filterTM f core_km)

instance Eq (DeBruijn (KindCoercion Zk)) where
  D env1 co1 == D env2 co2
    = D env1 (kiCoercionKind co1) == D env2 (kiCoercionKind co2)

lkKC :: DeBruijn CoreKindCoercion -> KindCoercionMapX a -> Maybe a
lkKC (D env co) (KindCoercionMapX core_km) = lkMK (D env $ kiCoercionKind co) core_km

xtKC :: DeBruijn CoreKindCoercion -> XT a -> KindCoercionMapX a -> KindCoercionMapX a
xtKC (D env co) f (KindCoercionMapX m)
  = KindCoercionMapX (xtMK (D env $ kiCoercionKind co) f m)

{- *********************************************************************
*                                                                      *
                   Kinds
*                                                                      *
********************************************************************** -}

type MonoKindMapG = GenMap MonoKindMapX

data MonoKindMapX a = MKM
  { mkm_var :: VarMap CoreKiVar a
  , mkm_bi :: Map.Map BuiltInKi a
  , mkm_pred :: Map.Map KiPredCon (MonoKindMapG (MonoKindMapG a))
  , mkm_fun :: Map.Map FunKiFlag (MonoKindMapG (MonoKindMapG a))
  }

instance Functor MonoKindMapX where
  fmap f MKM {..} = MKM
    { mkm_var = fmap f mkm_var
    , mkm_bi = fmap f mkm_bi
    , mkm_pred = fmap (fmap (fmap f)) mkm_pred
    , mkm_fun = fmap (fmap (fmap f)) mkm_fun }

instance TrieMap MonoKindMapX where
  type Key MonoKindMapX = DeBruijn CoreMonoKind
  emptyTM = emptyMK
  lookupTM = lkMK
  alterTM = xtMK
  foldTM = fdMK
  filterTM = filterMK

emptyMK :: MonoKindMapX a
emptyMK = MKM { mkm_var = emptyTM
              , mkm_bi = emptyTM
              , mkm_pred = emptyTM
              , mkm_fun = emptyTM }

lkMK :: DeBruijn CoreMonoKind -> MonoKindMapX a -> Maybe a
lkMK (D env ki) m = go ki m
  where
    go (KiVarKi v) = mkm_var >.> lkVar (\e b -> lookupCMEB e (Kv v)) env v
    go (BIKi bi) = mkm_bi >.> lookupTM bi
    go (KiPredApp p k1 k2) = mkm_pred >.> lookupTM p >=> lkG (D env k1) >=> lkG (D env k2)
    go (FunKi f k1 k2) = mkm_fun >.> lookupTM f >=> lkG (D env k1) >=> lkG (D env k2)

xtMK :: DeBruijn CoreMonoKind -> XT a -> MonoKindMapX a -> MonoKindMapX a
xtMK (D env (KiVarKi v)) f m
  = m { mkm_var = mkm_var m |> xtVar (\e b -> lookupCMEB e (Kv v)) env v f }
xtMK (D env (BIKi bi)) f m
  = m { mkm_bi = mkm_bi m |> alterTM bi f }
xtMK (D env (KiPredApp p k1 k2)) f m
  = m { mkm_pred = mkm_pred m |> alterTM p |>> xtG (D env k1) |>> xtG (D env k2) f }
xtMK (D env (FunKi fl k1 k2)) f m
  = m { mkm_fun = mkm_fun m |> alterTM fl |>> xtG (D env k1) |>> xtG (D env k2) f }

fdMK :: (a -> b -> b) -> MonoKindMapX a -> b -> b
fdMK k MKM {..} = foldTM k mkm_var
                  . foldTM k mkm_bi
                  . foldTM (foldTM (foldTM k)) mkm_pred
                  . foldTM (foldTM (foldTM k)) mkm_fun

filterMK :: (a -> Bool) -> MonoKindMapX a -> MonoKindMapX a
filterMK f MKM {..} = MKM
  { mkm_var = filterTM f mkm_var
  , mkm_bi = filterTM f mkm_bi
  , mkm_pred = fmap (fmap (filterTM f)) mkm_pred
  , mkm_fun = fmap (fmap (filterTM f)) mkm_fun }

instance Eq (DeBruijn (MonoKind Zk)) where
  (==) = eqDeBruijnMonoKind

instance Eq (DeBruijn (Kind Zk)) where
  (==) = eqDeBruijnKind

eqDeBruijnKind :: DeBruijn (Kind Zk) -> DeBruijn (Kind Zk) -> Bool
eqDeBruijnKind = go 
  where
    go (D env1 k1) (D env2 k2) = case (k1, k2) of
      (ForAllKi kv1 k1, ForAllKi kv2 k2)
       -> go (D (extendCMEB env1 (Kv kv1)) k1) (D (extendCMEB env2 (Kv kv2)) k2)
      (Mono m1, Mono m2)
        -> eqDeBruijnMonoKind (D env1 m1) (D env2 m2)
      _ -> False

eqDeBruijnMonoKind :: DeBruijn (MonoKind Zk) -> DeBruijn (MonoKind Zk) -> Bool
eqDeBruijnMonoKind = go
  where
    go (D env1 k1) (D env2 k2) = case (k1, k2) of
      (KiVarKi v1, KiVarKi v2) -> eqDeBruijnKv (D env1 v1) (D env2 v2)

      (BIKi b1, BIKi b2) -> b1 == b2

      (KiPredApp p k1 k2, KiPredApp p' k1' k2')
        -> p == p'
           && go (D env1 k1) (D env2 k1')
           && go (D env1 k2) (D env2 k2')

      (FunKi f k1 k2, FunKi f' k1' k2')
        -> f == f'
           && go (D env1 k1) (D env2 k1')
           && go (D env1 k2) (D env2 k2')

      _ -> False

{- *********************************************************************
*                                                                      *
                   Types
*                                                                      *
********************************************************************** -}

type TypeMapG = GenMap TypeMapX

data TypeMapX a = TM
  { tm_var :: VarMap (TyVar Zk) a
  , tm_app :: TypeMapG (TypeMapG a)
  , tm_kind :: MonoKindMapG a
  , tm_tycon :: DNameEnv a
  , tm_forall :: TypeMapG (LamBndrMap a)
  , tm_coerce :: Maybe a
  }

trieMapView :: CoreType -> Maybe CoreType
trieMapView ty
  | Just (tc, tys@(_:_)) <- splitTyConApp_maybe ty
  = Just $ foldl' AppTy (mkTyConTy tc) tys
  | Just ty' <- coreView ty
  = Just ty'
trieMapView _ = Nothing

instance Functor TypeMapX where
  fmap f TM {..} = TM
    { tm_var = fmap f tm_var
    , tm_app = fmap (fmap f) tm_app
    , tm_kind = fmap f tm_kind
    , tm_tycon = fmap f tm_tycon
    , tm_forall = fmap (fmap f) tm_forall
    , tm_coerce = fmap f tm_coerce }

instance TrieMap TypeMapX where
  type Key TypeMapX = DeBruijn CoreType
  emptyTM = emptyT
  lookupTM = lkT
  alterTM = xtT
  foldTM = fdT
  filterTM = filterT

instance {-# OVERLAPPING #-} Outputable a => Outputable (TypeMapG a) where
  ppr m = text "TypeMap elts" <+> ppr (foldTM (:) m [])

emptyT :: TypeMapX a
emptyT = TM { tm_var = emptyTM
            , tm_app = emptyTM
            , tm_kind = emptyTM
            , tm_tycon = emptyDNameEnv
            , tm_forall = emptyTM
            , tm_coerce = Nothing }

lkT :: DeBruijn CoreType -> TypeMapX a -> Maybe a
lkT (D env ty) m = go ty m
  where
    go ty | Just ty' <- trieMapView ty = go ty'
    go (TyVarTy v) = tm_var >.> lkVar (\e b -> lookupCMEB e (Tv b)) env v
    go (AppTy t1 t2) = tm_app >.> lkG (D env t1) >=> lkG (D env t2)
    go (Embed ki) = tm_kind >.> lkG (D env ki)
    go (TyConApp tc []) = tm_tycon >.> lkDNamed tc
    go (ForAllTy (Bndr tv _) ty) = tm_forall >.> lkG (D (extendCMEB env (Tv tv)) ty)
                                             >=> lkLamBndr env (Tv tv, Nothing)
    go (ForAllKiCo kcv ty) = tm_forall >.> lkG (D (extendCMEB env (KCv kcv)) ty)
                                       >=> lkLamBndr env (KCv kcv, Nothing)
    go (BigTyLamTy kv ty) = tm_forall >.> lkG (D (extendCMEB env (Kv kv)) ty)
                                      >=> lkLamBndr env (Kv kv, Nothing)
    go (CastTy t _) = go t
    go KindCoercion{} = tm_coerce
    go ty@(TyConApp _ (_:_)) = pprPanic "lkT TyConApp" (ppr ty)
    go ty@FunTy{} = pprPanic "lkT FunTy" (ppr ty)
    go ty@TyLamTy{} = pprPanic "lkT TyLamTy" (ppr ty)

xtT :: DeBruijn CoreType -> XT a -> TypeMapX a -> TypeMapX a
xtT (D env ty) f m | Just ty' <- trieMapView ty = xtT (D env ty') f m
xtT (D env (TyVarTy v)) f m
  = m { tm_var = tm_var m |> xtVar (\e b -> lookupCMEB e (Tv b)) env v f }
xtT (D env (AppTy t1 t2)) f m = m { tm_app = tm_app m |> xtG (D env t1) |>> xtG (D env t2) f }
xtT (D env (Embed ki)) f m = m { tm_kind = tm_kind m |> xtG (D env ki) f }
xtT (D _ (TyConApp tc [])) f m = m { tm_tycon = tm_tycon m |> xtDNamed tc f }
xtT (D env (CastTy t _)) f m = xtT (D env t) f m
xtT (D _ KindCoercion{}) f m = m { tm_coerce = tm_coerce m |> f }
xtT (D env (ForAllTy (Bndr tv _) ty)) f m
  = m { tm_forall = tm_forall m |> xtG (D (extendCMEB env (Tv tv)) ty)
                    |>> xtLamBndr env (Tv tv, Nothing) f }
xtT (D env (ForAllKiCo kcv ty)) f m
  = m { tm_forall = tm_forall m |> xtG (D (extendCMEB env (KCv kcv)) ty)
                    |>> xtLamBndr env (KCv kcv, Nothing) f }
xtT (D env (BigTyLamTy kv ty)) f m
  = m { tm_forall = tm_forall m |> xtG (D (extendCMEB env (Kv kv)) ty)
                    |>> xtLamBndr env (Kv kv, Nothing) f }
xtT (D _ ty@(TyConApp _ (_:_))) _ _ = pprPanic "xtT TyConApp" (ppr ty)
xtT (D _ ty@FunTy{}) _ _ = pprPanic "xtT FunTy" (ppr ty)
xtT (D _ ty@TyLamTy{}) _ _ = pprPanic "xtT TyLamTy" (ppr ty)

fdT :: (a -> b -> b) -> TypeMapX a -> b -> b
fdT k TM {..} = foldTM k tm_var
                . foldTM (foldTM k) tm_app
                . foldTM k tm_kind
                . foldTM k tm_tycon
                . foldTM (foldTM k) tm_forall
                . foldMaybe k tm_coerce

filterT :: (a -> Bool) -> TypeMapX a -> TypeMapX a
filterT f TM {..} = TM
  { tm_var = filterTM f tm_var
  , tm_app = fmap (filterTM f) tm_app
  , tm_kind = filterTM f tm_kind
  , tm_tycon = filterTM f tm_tycon
  , tm_forall = fmap (filterTM f) tm_forall
  , tm_coerce = filterMaybe f tm_coerce }

instance Eq (DeBruijn (Type Zk)) where
  (==) = eqDeBruijnType

data TypeEquality = TNEQ | TEQ | TEQX

eqDeBruijnType :: DeBruijn (Type Zk) -> DeBruijn (Type Zk) -> Bool
eqDeBruijnType env_t1@(D env1 t1) env_t2@(D env2 t2)
  = case go env_t1 env_t2 of
      TEQX -> eqDeBruijnKind (D env1 k1) (D env2 k2)
      ty_eq -> toBool ty_eq
  where
    k1 = typeKind t1
    k2 = typeKind t2

    toBool TNEQ = False
    toBool _ = True

    liftEquality False = TNEQ
    liftEquality _ = TEQ

    hasCast TEQ = TEQX
    hasCast eq = eq

    andEq TNEQ _ = TNEQ
    andEq TEQX e = hasCast e
    andEq TEQ e = e

    go (D env1 (TyConApp tc1 tys1)) (D env2 (TyConApp tc2 tys2))
      | tc1 == tc2, not (isForgetfulSynTyCon tc1)
      = gos env1 env2 tys1 tys2

    go env_t@(D env t) env_t'@(D env' t')
      | Just new_t <- coreView t = go (D env new_t) env_t'
      | Just new_t' <- coreView t' = go env_t (D env' new_t')
      | otherwise
      = case (t, t') of
          (CastTy t1 _, _) -> hasCast (go (D env t1) (D env t'))
          (_, CastTy t1' _) -> hasCast (go (D env t) (D env t1'))

          (TyVarTy v, TyVarTy v')
            -> liftEquality $ eqDeBruijnTv (D env v) (D env' v')

          (AppTy t1 t2, s)
            | Just (t1', t2') <- splitAppTyNoView_maybe s
              -> go (D env t1) (D env' t1') `andEq` go (D env t2) (D env' t2')
          (s, AppTy t1' t2')
            | Just (t1, t2) <- splitAppTyNoView_maybe s
              -> go (D env t1) (D env t1') `andEq` go (D env t2) (D env' t2')

          (FunTy k1 t1 t2, FunTy k1' t1' t2')
            -> liftEquality (eqDeBruijnMonoKind (D env k1) (D env' k1')) `andEq`
               liftEquality (eqDeBruijnType (D env t1) (D env' t1')) `andEq`
               liftEquality (eqDeBruijnType (D env t2) (D env' t2'))

          (TyConApp tc tys, TyConApp tc' tys')
            -> liftEquality (tc == tc') `andEq` gos env env' tys tys'

          (ForAllTy (Bndr tv vis) ty, ForAllTy (Bndr tv' vis') ty')
            -> liftEquality (vis `eqForAllVis` vis') `andEq`
               liftEquality (eqDeBruijnMonoKind (D env (varKind tv)) (D env' (varKind tv')))
               `andEq`
               go (D (extendCMEB env (Tv tv)) ty) (D (extendCMEB env' (Tv tv')) ty')

          (ForAllKiCo kcv ty, ForAllKiCo kcv' ty')
            -> liftEquality (eqDeBruijnMonoKind (D env (varKind kcv)) (D env' (varKind kcv')))
               `andEq`
               go (D (extendCMEB env (KCv kcv)) ty) (D (extendCMEB env' (KCv kcv')) ty')

          (BigTyLamTy kv ty, BigTyLamTy kv' ty')
            -> go (D (extendCMEB env (Kv kv)) ty) (D (extendCMEB env' (Kv kv')) ty')

          (Embed k, Embed k')
            -> liftEquality (eqDeBruijnMonoKind (D env k) (D env' k'))

          (KindCoercion{}, KindCoercion{}) -> TEQ

          _ -> TNEQ

    gos !_ !_ [] [] = TEQ
    gos e1 e2 (ty1:tys1) (ty2:tys2) = go (D e1 ty1) (D e2 ty2) `andEq`
                                      gos e1 e2 tys1 tys2
    gos _ _ _ _ = TNEQ

instance Eq (DeBruijn (Id Zk)) where
  (==) = eqDeBruijnId

instance Eq (DeBruijn (TyVar Zk)) where
  (==) = eqDeBruijnTv

instance Eq (DeBruijn (KiCoVar Zk)) where
  (==) = eqDeBruijnKCv

instance Eq (DeBruijn (KiVar Zk)) where
  (==) = eqDeBruijnKv

instance Eq (DeBruijn CoreBndr) where
  (==) = eqDeBruijnBndr

eqDeBruijnBndr :: DeBruijn CoreBndr -> DeBruijn CoreBndr -> Bool
eqDeBruijnBndr (D env1 v1) (D env2 v2)
  = case (lookupCMEB env1 v1, lookupCMEB env2 v2) of
      (Just b1, Just b2) -> b1 == b2
      (Nothing, Nothing) -> v1 == v2
      _ -> False

eqDeBruijnId :: DeBruijn (Id Zk) -> DeBruijn (Id Zk) -> Bool
eqDeBruijnId (D env1 v1) (D env2 v2) = eqDeBruijnBndr (D env1 (C.Id v1)) (D env2 (C.Id v2))

eqDeBruijnTv :: DeBruijn (TyVar Zk) -> DeBruijn (TyVar Zk) -> Bool
eqDeBruijnTv (D env1 v1) (D env2 v2) = eqDeBruijnBndr (D env1 (Tv v1)) (D env2 (Tv v2))

eqDeBruijnKCv :: DeBruijn (KiCoVar Zk) -> DeBruijn (KiCoVar Zk) -> Bool
eqDeBruijnKCv (D env1 v1) (D env2 v2) = eqDeBruijnBndr (D env1 (KCv v1)) (D env2 (KCv v2))

eqDeBruijnKv :: DeBruijn (KiVar Zk) -> DeBruijn (KiVar Zk) -> Bool
eqDeBruijnKv (D env1 v1) (D env2 v2) = eqDeBruijnBndr (D env1 (Kv v1)) (D env2 (Kv v2))

{- *********************************************************************
*                                                                      *
                   Variables
*                                                                      *
********************************************************************* -}

type BoundVar = Int
type BoundVarMap a = IntMap.IntMap a

data CmEnv = CME
  { cme_next :: !BoundVar -- Same numbers used across all types of vars for utility in 'eqDeBruijnBndr'
  , cme_id_env :: VarEnv (Id Zk) BoundVar
  , cme_tv_env :: VarEnv (TyVar Zk) BoundVar
  , cme_kcv_env :: VarEnv (KiCoVar Zk) BoundVar
  , cme_kv_env :: VarEnv (KiVar Zk) BoundVar
  }

emptyCME :: CmEnv
emptyCME = CME { cme_next = 0
               , cme_id_env = emptyVarEnv
               , cme_tv_env = emptyVarEnv
               , cme_kcv_env = emptyVarEnv
               , cme_kv_env = emptyVarEnv
               }

extendCME :: CmEnv -> Id Zk -> CmEnv
extendCME cme@CME{ cme_next = bv, cme_id_env = env } v
  = cme { cme_next = bv + 1, cme_id_env = extendVarEnv env v bv }

extendCMEs :: CmEnv -> [Id Zk] -> CmEnv
extendCMEs env vs = foldl' extendCME env vs

extendCMEB :: CmEnv -> CoreBndr -> CmEnv
extendCMEB cme@CME{ cme_next = bv
                  , cme_id_env = ids
                  , cme_tv_env = tvs
                  , cme_kcv_env = kcvs
                  , cme_kv_env = kvs } v
  = case v of
      C.Id id -> cme { cme_next = bv + 1, cme_id_env = extendVarEnv ids id bv }
      Tv tv -> cme { cme_next = bv + 1, cme_tv_env = extendVarEnv tvs tv bv }
      KCv kcv -> cme { cme_next = bv + 1, cme_kcv_env = extendVarEnv kcvs kcv bv }
      Kv kv -> cme { cme_next = bv + 1, cme_kv_env = extendVarEnv kvs kv bv }

lookupCME :: CmEnv -> CoreId -> Maybe BoundVar
lookupCME CME{ cme_id_env = env } v = lookupVarEnv env v

lookupCMEB :: CmEnv -> CoreBndr -> Maybe BoundVar
lookupCMEB cme b = case b of
  C.Id v -> lookupVarEnv (cme_id_env cme) v
  Tv v -> lookupVarEnv (cme_tv_env cme) v
  KCv v -> lookupVarEnv (cme_kcv_env cme) v
  Kv v -> lookupVarEnv (cme_kv_env cme) v

data DeBruijn a = D CmEnv a

deBruijnize :: a -> DeBruijn a
deBruijnize = D emptyCME

instance Eq (DeBruijn a) => Eq (DeBruijn [a]) where
  D _ [] == D _ [] = True
  D env (x:xs) == D env' (x':xs')
    = D env x == D env' x'
      && D env xs == D env' xs'
  _ == _ = False

instance Eq (DeBruijn a) => Eq (DeBruijn (Maybe a)) where
  D _ Nothing == D _ Nothing = True
  D env (Just x) == D env' (Just x') = D env x == D env' x'
  _ == _ = False

data BndrMap a = BndrMap (TypeMapG a)

instance Functor BndrMap where
  fmap f = \(BndrMap tm) -> BndrMap (fmap f tm)
  {-# INLINE fmap #-}

instance TrieMap BndrMap where
  type Key BndrMap = CoreId
  emptyTM = BndrMap emptyTM
  lookupTM = lkIdBndr emptyCME
  alterTM = xtIdBndr emptyCME
  foldTM = fdBndrMap
  filterTM = ftBndrMap

fdBndrMap :: (a -> b -> b) -> BndrMap a -> b -> b
fdBndrMap f (BndrMap tm) = foldTM f tm 

lkIdBndr :: CmEnv -> CoreId -> BndrMap a -> Maybe a
lkIdBndr env v (BndrMap tymap) = lkG (D env (varType v)) tymap

xtIdBndr :: CmEnv -> CoreId -> XT a -> BndrMap a -> BndrMap a
xtIdBndr env v xt (BndrMap tymap) = BndrMap (xtG (D env (varType v)) xt tymap)

ftBndrMap :: (a -> Bool) -> BndrMap a -> BndrMap a
ftBndrMap f (BndrMap tm) = BndrMap (filterTM f tm)

data LamBndrMap a
  = LamBndrMap (MaybeMap (EitherMap TypeMapG MonoKindMapG) (MaybeMap MonoKindMapG a))

instance Functor LamBndrMap where
  fmap f = \(LamBndrMap tm) -> LamBndrMap (fmap (fmap f) tm)
  {-# INLINE fmap #-}

instance TrieMap LamBndrMap where
  type Key LamBndrMap = (CoreBndr, Maybe CoreMonoKind)
  emptyTM = LamBndrMap emptyTM
  lookupTM = lkLamBndr emptyCME
  alterTM = xtLamBndr emptyCME
  foldTM = fdLamBndrMap
  filterTM = ftLamBndrMap

fdLamBndrMap :: (a -> b -> b) -> LamBndrMap a -> b -> b
fdLamBndrMap f (LamBndrMap tm) = foldTM (foldTM f) tm

lkLamBndr :: CmEnv -> (CoreBndr, Maybe CoreMonoKind) -> LamBndrMap a -> Maybe a
lkLamBndr env (v, k) (LamBndrMap map) = do
  let key = case v of
              C.Id v -> Just (Left (D env (varType v)))
              Tv v -> Just (Right (D env (varKind v)))
              KCv v -> Just (Right (D env (varKind v)))
              Kv _ -> Nothing
  multmap <- lookupTM key map
  lookupTM (D env <$> k) multmap

xtLamBndr :: CmEnv -> (CoreBndr, Maybe CoreMonoKind) -> XT a -> LamBndrMap a -> LamBndrMap a
xtLamBndr env (v, k) xt (LamBndrMap mm) =
  let key1 = case v of
              C.Id v -> Just (Left (D env (varType v)))
              Tv v -> Just (Right (D env (varKind v)))
              KCv v -> Just (Right (D env (varKind v)))
              Kv _ -> Nothing
      key2 = D env <$> k
  in LamBndrMap (mm |> alterTM key1 |>> (alterTM key2 xt))

ftLamBndrMap :: (a -> Bool) -> LamBndrMap a -> LamBndrMap a
ftLamBndrMap f (LamBndrMap mm) = LamBndrMap (fmap (filterTM f) mm)

data VarMap v a = VM
  { vm_bvar :: BoundVarMap a
  , vm_fvar :: DVarEnv v a
  }

instance Functor (VarMap v) where
  fmap f VM {..} = VM
    { vm_bvar = fmap f vm_bvar
    , vm_fvar = fmap f vm_fvar }

instance TrieMap (VarMap CoreId) where
  type Key (VarMap CoreId) = CoreId
  emptyTM = VM { vm_bvar = IntMap.empty, vm_fvar = emptyDVarEnv }
  lookupTM = lkVar lookupCME emptyCME
  alterTM = xtVar lookupCME emptyCME
  foldTM = fdVar
  filterTM = ftVar

instance TrieMap (VarMap CoreTyVar) where
  type Key (VarMap CoreTyVar) = CoreTyVar
  emptyTM = VM { vm_bvar = IntMap.empty, vm_fvar = emptyDVarEnv }
  lookupTM = lkVar (\e b -> lookupCMEB e (Tv b)) emptyCME
  alterTM = xtVar (\e b -> lookupCMEB e (Tv b)) emptyCME
  foldTM = fdVar
  filterTM = ftVar

instance TrieMap (VarMap CoreKiVar) where
  type Key (VarMap CoreKiVar) = CoreKiVar
  emptyTM = VM { vm_bvar = IntMap.empty, vm_fvar = emptyDVarEnv }
  lookupTM = lkVar (\e b -> lookupCMEB e (Kv b)) emptyCME
  alterTM = xtVar (\e b -> lookupCMEB e (Kv b)) emptyCME
  foldTM = fdVar
  filterTM = ftVar

lkVar :: Uniquable v => (CmEnv -> v -> Maybe BoundVar) -> CmEnv -> v -> VarMap v a -> Maybe a
lkVar lookup env v
  | Just bv <- lookup env v = vm_bvar >.> lookupTM bv
  | otherwise = vm_fvar >.> lkDFreeVar v 

xtVar
  :: Uniquable v
  => (CmEnv -> v -> Maybe BoundVar)
  -> CmEnv -> v -> XT a -> VarMap v a -> VarMap v a
xtVar lookup env v f m
  | Just bv <- lookup env v = m { vm_bvar = vm_bvar m |> alterTM bv f }
  | otherwise = m { vm_fvar = vm_fvar m |> xtDFreeVar v f }

fdVar :: Uniquable v => (a -> b -> b) -> VarMap v a -> b -> b
fdVar k m = foldTM k (vm_bvar m)
            . foldTM k (vm_fvar m)

lkDFreeVar :: Uniquable v => v -> DVarEnv v a -> Maybe a
lkDFreeVar var env = lookupDVarEnv env var

xtDFreeVar :: Uniquable v => v -> XT a -> DVarEnv v a -> DVarEnv v a
xtDFreeVar v f m = alterDVarEnv f m v

ftVar :: Uniquable v => (a -> Bool) -> VarMap v a -> VarMap v a
ftVar f VM {..} = VM
  { vm_bvar = filterTM f vm_bvar
  , vm_fvar = filterTM f vm_fvar }

lkDNamed :: NamedThing n => n -> DNameEnv a -> Maybe a
lkDNamed n env = lookupDNameEnv env (getName n)

xtDNamed :: NamedThing n => n -> XT a -> DNameEnv a -> DNameEnv a
xtDNamed tc f m = alterDNameEnv f m (getName tc)
