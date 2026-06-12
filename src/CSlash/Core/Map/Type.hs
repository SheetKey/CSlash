{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Map.Type where

import CSlash.Cs.Pass

import CSlash.Core as C
import CSlash.Core.Type
import CSlash.Core.Type.Rep
import CSlash.Core.Kind
import CSlash.Core.TyCon( isForgetfulSynTyCon )
import CSlash.Data.TrieMap

import CSlash.Data.FastString
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Unique.FM
import CSlash.Utils.Outputable

import CSlash.Utils.Panic

import qualified Data.Map    as Map
import qualified Data.IntMap as IntMap

import Control.Monad ( (>=>) )

-- {-# SPECIALIZE lkG :: Key TypeMapX     -> TypeMapG a     -> Maybe a #-}
-- {-# SPECIALIZE lkG :: Key CoercionMapX -> CoercionMapG a -> Maybe a #-}
-- 
-- {-# SPECIALIZE xtG :: Key TypeMapX     -> XT a -> TypeMapG a -> TypeMapG a #-}
-- {-# SPECIALIZE xtG :: Key CoercionMapX -> XT a -> CoercionMapG a -> CoercionMapG a #-}
-- 
-- {-# SPECIALIZE mapG :: (a -> b) -> TypeMapG a     -> TypeMapG b #-}
-- {-# SPECIALIZE mapG :: (a -> b) -> CoercionMapG a -> CoercionMapG b #-}
-- 
-- {-# SPECIALIZE fdG :: (a -> b -> b) -> TypeMapG a     -> b -> b #-}
-- {-# SPECIALIZE fdG :: (a -> b -> b) -> CoercionMapG a -> b -> b #-}

{- *********************************************************************
*                                                                      *
                   Coercions
*                                                                      *
********************************************************************* -}

instance Eq (DeBruijn (TypeCoercion Zk)) where
  D env1 co1 == D env2 co2
    = D env1 (tycoercionType co1) == D env2 (tycoercionType co2)

{- *********************************************************************
*                                                                      *
                   Kinds
*                                                                      *
********************************************************************** -}

type MonoKindMapG = GenMap MonoKindMapX

data MonoKindMapX a = MKM

instance Functor MonoKindMapX

instance TrieMap MonoKindMapX where
  type Key MonoKindMapX = DeBruijn CoreMonoKind

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
  -- { tm_var :: VarMap (TyVar Zk) a
  -- , tm_app :: TypeMapG (TypeMapG a)
  -- , tm_tycon :: DNameEnv a
  -- , tm_forall :: TypeMapG (BndrMap a)

instance Functor TypeMapX

instance TrieMap TypeMapX where
  type Key TypeMapX = DeBruijn CoreType

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
