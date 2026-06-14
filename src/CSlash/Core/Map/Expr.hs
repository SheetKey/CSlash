{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module CSlash.Core.Map.Expr where

import CSlash.Data.TrieMap
import CSlash.Core.Map.Type
import CSlash.Core as C
import CSlash.Core.Type
import CSlash.Types.Tickish
import CSlash.Types.Var

import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Outputable

import qualified Data.Map    as Map
import CSlash.Types.Name.Env
import Control.Monad( (>=>) )
import CSlash.Types.Literal (Literal)

-- {-# SPECIALIZE lkG :: Key CoreMapX     -> CoreMapG a     -> Maybe a #-}
-- {-# SPECIALIZE xtG :: Key CoreMapX     -> XT a -> CoreMapG a -> CoreMapG a #-}
-- {-# SPECIALIZE mapG :: (a -> b) -> CoreMapG a     -> CoreMapG b #-}
-- {-# SPECIALIZE fdG :: (a -> b -> b) -> CoreMapG a     -> b -> b #-}

{- *********************************************************************
*                                                                      *
                   CoreMap
*                                                                      *
********************************************************************* -}

newtype CoreMap a = CoreMap (CoreMapG a)

type CoreMapG = GenMap CoreMapX

data CoreMapX a = CM
  { cm_id :: VarMap CoreId a
  , cm_lit :: LiteralMap a
  , cm_kco :: KindCoercionMapG a
  , cm_type :: TypeMapG a
  , cm_kind :: MonoKindMapG a
  , cm_cast :: CoreMapG (TypeCoercionMapG a)
  , cm_tick :: CoreMapG (TickishMap a)
  , cm_app :: CoreMapG (CoreMapG a)
  , cm_lam :: CoreMapG (LamBndrMap a)
  , cm_letn :: CoreMapG (CoreMapG (BndrMap a))
  , cm_letr :: ListMap CoreMapG (CoreMapG (ListMap BndrMap a))
  , cm_case :: CoreMapG (ListMap AltMap a)
  }

type LiteralMap a = Map.Map Literal a

instance Eq (DeBruijn CoreExpr) where
  (==) = eqDeBruijnExpr

eqDeBruijnExpr :: DeBruijn CoreExpr -> DeBruijn CoreExpr -> Bool
eqDeBruijnExpr (D env1 e1) (D env2 e2) = go e1 e2
  where
    go (Var v1) (Var v2) = eqDeBruijnId (D env1 v1) (D env2 v2)
    go (Lit lit1) (Lit lit2) = lit1 == lit2
    go (Type t1) (Type t2) = eqDeBruijnType (D env1 t1) (D env2 t2)
    go KiCo{} KiCo{} = True
    go (Kind k1) (Kind k2) = eqDeBruijnMonoKind (D env1 k1) (D env2 k2)
    go (Cast e1 co1) (Cast e2 co2) = D env1 co1 == D env2 co2 && go e1 e2
    go (App f1 a1) (App f2 a2) = go f1 f2 && go a1 a2
    go (Tick n1 e1) (Tick n2 e2)
      = eqDeBruijnTickish (D env1 n1) (D env2 n2)
        && go e1 e2
    go (Lam b1 k1 e1) (Lam b2 k2 e2)
      = eqDeBruijnLamBndr (D env1 (b1, k1)) (D env2 (b2, k2))
        && eqDeBruijnExpr (D (extendCMEB env1 b1) e1) (D (extendCMEB env2 b2) e2)
    go (Let (NonRec v1 r1) e1) (Let (NonRec v2 r2) e2)
      = go r1 r2
        && eqDeBruijnExpr (D (extendCME env1 v1) e1) (D (extendCME env2 v2) e2)
    go (Let (Rec ps1) e1) (Let (Rec ps2) e2)
      = equalLength ps1 ps2
        && all2 (\b1 b2 -> eqDeBruijnType (D env1 (varType b1)) (D env2 (varType b2))) bs1 bs2
        && D env1' rs1 == D env2' rs2
        && eqDeBruijnExpr (D env1' e1) (D env2' e2)
      where
        (bs1, rs1) = unzip ps1
        (bs2, rs2) = unzip ps2
        env1' = extendCMEs env1 bs1
        env2' = extendCMEs env2 bs2                           
    go (Case e1 b1 t1 a1) (Case e2 b2 t2 a2)
      | null a1
      = null a2 && go e1 e2 && D env1 t1 == D env2 t2
      | otherwise
      = go e1 e2 && D (extendCME env1 b1) a1 == D (extendCME env2 b2) a2
    go _ _ = False

eqDeBruijnLamBndr
  :: DeBruijn (CoreBndr, Maybe CoreMonoKind)
  -> DeBruijn (CoreBndr, Maybe CoreMonoKind)
  -> Bool
eqDeBruijnLamBndr (D env1 a1) (D env2 a2) = go a1 a2
  where
    go (C.Id b1, Just k1) (C.Id b2, Just k2)
      = eqDeBruijnType (D env1 (varType b1)) (D env2 (varType b2))
        && D env1 k1 == D env2 k2
    go (Tv b1, Nothing) (Tv b2, Nothing)
      = eqDeBruijnMonoKind (D env1 (varKind b1)) (D env2 (varKind b2))
    go (KCv b1, Nothing) (KCv b2, Nothing)
      = eqDeBruijnMonoKind (D env1 (varKind b1)) (D env2 (varKind b2))
    go (Kv _, Nothing) (Kv _, Nothing) = True
    go _ _ = False

eqDeBruijnTickish :: DeBruijn CoreTickish -> DeBruijn CoreTickish -> Bool
eqDeBruijnTickish (D env1 t1) (D env2 t2) = go t1 t2
  where
    go l@CpcTick{} r@CpcTick{} = l == r

eqCoreExpr :: CoreExpr -> CoreExpr -> Bool
eqCoreExpr e1 e2 = eqDeBruijnExpr (deBruijnize e1) (deBruijnize e2)

instance Outputable a => Outputable (CoreMap a) where
  ppr m = text "CoreMap elts" <+> ppr (foldTM (:) m [])

instance Functor CoreMap where
  fmap f = \(CoreMap m) -> CoreMap (fmap f m)
  {-# INLINE fmap #-}

instance TrieMap CoreMap where
  type Key CoreMap = CoreExpr
  emptyTM = CoreMap emptyTM
  lookupTM k (CoreMap m) = lookupTM (deBruijnize k) m
  alterTM k f (CoreMap m) = CoreMap (alterTM (deBruijnize k) f m)
  foldTM k (CoreMap m) = foldTM k m
  filterTM f (CoreMap m) = CoreMap (filterTM f m)

lookupCoreMap :: CoreMap a -> CoreExpr -> Maybe a
lookupCoreMap cm e = lookupTM e cm

extendCoreMap :: CoreMap a -> CoreExpr -> a -> CoreMap a
extendCoreMap m e v = alterTM e (\_ -> Just v) m

emptyCoreMap :: CoreMap a
emptyCoreMap = emptyTM

emptyE :: CoreMapX a
emptyE = CM
  { cm_id = emptyTM
  , cm_lit = emptyTM
  , cm_kco = emptyTM
  , cm_type = emptyTM
  , cm_kind = emptyTM
  , cm_cast = emptyTM
  , cm_app = emptyTM
  , cm_lam = emptyTM
  , cm_letn = emptyTM
  , cm_letr = emptyTM
  , cm_case = emptyTM
  , cm_tick = emptyTM }

instance Functor CoreMapX where
  fmap f CM {..} = CM
    { cm_id = fmap f cm_id
    , cm_lit = fmap f cm_lit
    , cm_kco = fmap f cm_kco
    , cm_type = fmap f cm_type
    , cm_kind = fmap f cm_kind
    , cm_cast = fmap (fmap f) cm_cast
    , cm_app = fmap (fmap f) cm_app
    , cm_lam = fmap (fmap f) cm_lam
    , cm_letn = fmap (fmap (fmap f)) cm_letn
    , cm_letr = fmap (fmap (fmap f)) cm_letr
    , cm_case = fmap (fmap f) cm_case
    , cm_tick = fmap (fmap f) cm_tick }

instance TrieMap CoreMapX where
  type Key CoreMapX = DeBruijn CoreExpr
  emptyTM = emptyE
  lookupTM = lkE
  alterTM = xtE
  foldTM = fdE
  filterTM = ftE

ftE :: (a -> Bool) -> CoreMapX a -> CoreMapX a
ftE f CM {..} = CM
  { cm_id = filterTM f cm_id
  , cm_lit = filterTM f cm_lit
  , cm_kco = filterTM f cm_kco
  , cm_type = filterTM f cm_type
  , cm_kind = filterTM f cm_kind
  , cm_cast = fmap (filterTM f) cm_cast
  , cm_app = fmap (filterTM f) cm_app
  , cm_lam = fmap (filterTM f) cm_lam
  , cm_letn = fmap (fmap (filterTM f)) cm_letn
  , cm_letr = fmap (fmap (filterTM f)) cm_letr
  , cm_case = fmap (filterTM f) cm_case
  , cm_tick = fmap (filterTM f) cm_tick }

fdE :: (a -> b -> b) -> CoreMapX a -> b -> b
fdE k CM {..} =
  foldTM k cm_id
  . foldTM k cm_lit
  . foldTM k cm_kco
  . foldTM k cm_type
  . foldTM k cm_kind
  . foldTM (foldTM k) cm_cast
  . foldTM (foldTM k) cm_tick
  . foldTM (foldTM k) cm_app
  . foldTM (foldTM k) cm_lam
  . foldTM (foldTM (foldTM k)) cm_letn
  . foldTM (foldTM (foldTM k)) cm_letr
  . foldTM (foldTM k) cm_case
  

lkE :: DeBruijn CoreExpr -> CoreMapX a -> Maybe a
lkE (D env expr) cm = go expr cm
  where
    go (Var v) = cm_id >.> lkVar lookupCME env v
    go (Lit l) = cm_lit >.> lookupTM l
    go (Type t) = cm_type >.> lkG (D env t)
    go (KiCo c) = cm_kco >.> lkG (D env c)
    go (Kind k) = cm_kind >.> lkG (D env k)
    go (Cast e c) = cm_cast >.> lkG (D env e) >=> lkG (D env c)
    go (Tick tickish e) = cm_tick >.> lkG (D env e) >=> lkTickish tickish
    go (App e1 e2) = cm_app >.> lkG (D env e2) >=> lkG (D env e1)
    go (Lam v k e) = cm_lam >.> lkG (D (extendCMEB env v) e)
                     >=> lkLamBndr env (v, k)
    go (Let (NonRec b r) e) = cm_letn >.> lkG (D env r)
                              >=> lkG (D (extendCME env b) e)
                              >=> lkIdBndr env b
    go (Let (Rec prs) e) = let (bndrs, rhss) = unzip prs
                               env1 = extendCMEs env bndrs
                           in cm_letr >.> lkList (lkG . D env1) rhss
                              >=> lkG (D env1 e)
                              >=> lkList (lkIdBndr env1) bndrs
    go (Case e b ty as)
      | null as = panic "empty case"
      | otherwise = cm_case >.> lkG (D env e) >=> lkList (lkA (extendCME env b)) as

xtE :: DeBruijn CoreExpr -> XT a -> CoreMapX a -> CoreMapX a
xtE (D env (Var v)) f m = m { cm_id = cm_id m |> xtVar lookupCME env v f }
xtE (D env (Type t)) f m = m { cm_type = cm_type m |> xtG (D env t) f }
xtE (D env (KiCo c)) f m = m { cm_kco = cm_kco m |> xtG (D env c) f }
xtE (D env (Kind k)) f m = m { cm_kind = cm_kind m |> xtG (D env k) f }
xtE (D _ (Lit l)) f m = m { cm_lit = cm_lit m |> alterTM l f }
xtE (D env (Cast e c)) f m = m { cm_cast = cm_cast m |> xtG (D env e) |>> xtG (D env c) f }
xtE (D env (Tick t e)) f m = m { cm_tick = cm_tick m|> xtG (D env e) |>> xtTickish t f }
xtE (D env (App e1 e2)) f m = m { cm_app = cm_app m |> xtG (D env e2) |>> xtG (D env e1) f }
xtE (D env (Lam v k e)) f m = m { cm_lam = cm_lam m |> xtG (D (extendCMEB env v) e)
                                          |>> xtLamBndr env (v, k) f }
xtE (D env (Let (NonRec b r) e)) f m = m { cm_letn = cm_letn m
                                                     |> xtG (D (extendCME env b) e)
                                                     |>> xtG (D env r)
                                                     |>> xtIdBndr env b f }
xtE (D env (Let (Rec prs) e)) f m = m { cm_letr = let (bndrs, rhss) = unzip prs
                                                      env1 = extendCMEs env bndrs
                                                  in cm_letr m
                                                     |> xtList (xtG . D env1) rhss
                                                     |>> xtG (D env1 e)
                                                     |>> xtList (xtIdBndr env1) bndrs f }
xtE (D env (Case e b ty as)) f m
  | null as = panic "empty case"
  | otherwise = m { cm_case = cm_case m |> xtG (D env e)
                              |>> let env1 = extendCME env b in xtList (xtA env1) as f }

type TickishMap a = Map.Map CoreTickish a

lkTickish :: CoreTickish -> TickishMap a -> Maybe a
lkTickish = lookupTM

xtTickish :: CoreTickish -> XT a -> TickishMap a -> TickishMap a
xtTickish = alterTM

data AltMap a = AM
  { am_deflt :: CoreMapG a
  , am_data :: DNameEnv (CoreMapG a)
  , am_lit :: LiteralMap (CoreMapG a) }

instance Functor AltMap where
  fmap f AM {..} = AM
    { am_deflt = fmap f am_deflt
    , am_data = fmap (fmap f) am_data
    , am_lit = fmap (fmap f) am_lit }

instance TrieMap AltMap where
  type Key AltMap = CoreAlt
  emptyTM = AM { am_deflt = emptyTM
               , am_data = emptyDNameEnv
               , am_lit = emptyTM }
  lookupTM = lkA emptyCME
  alterTM = xtA emptyCME
  foldTM = fdA
  filterTM = ftA

instance Eq (DeBruijn CoreAlt) where
  D env1 a1 == D env2 a2 = go a1 a2
    where
      go (Alt DEFAULT _ rhs1) (Alt DEFAULT _ rhs2) = D env1 rhs1 == D env2 rhs2
      go (Alt (LitAlt lit1) _ rhs1) (Alt (LitAlt lit2) _ rhs2)
        = lit1 == lit2 && D env1 rhs1 == D env2 rhs2
      go (Alt (DataAlt dc1) bs1 rhs1) (Alt (DataAlt dc2) bs2 rhs2)
        = dc1 == dc2 &&
          D (extendCMEs env1 bs1) rhs1 == D (extendCMEs env2 bs2) rhs2
      go _ _ = False

ftA :: (a -> Bool) -> AltMap a -> AltMap a
ftA f AM {..} = AM
  { am_deflt = filterTM f am_deflt
  , am_data = fmap (filterTM f) am_data
  , am_lit = fmap (filterTM f) am_lit }

lkA :: CmEnv -> CoreAlt -> AltMap a -> Maybe a
lkA env (Alt DEFAULT _ rhs) = am_deflt >.> lkG (D env rhs)
lkA env (Alt (LitAlt lit) _ rhs) = am_lit >.> lookupTM lit >=> lkG (D env rhs)
lkA env (Alt (DataAlt dc) bs rhs) = am_data >.> lkDNamed dc >=> lkG (D (extendCMEs env bs) rhs)

xtA :: CmEnv -> CoreAlt -> XT a -> AltMap a -> AltMap a
xtA env (Alt DEFAULT _ rhs) f m = m { am_deflt = am_deflt m |> xtG (D env rhs) f }
xtA env (Alt (LitAlt l) _ rhs) f m = m { am_lit = am_lit m |> alterTM l |>> xtG (D env rhs) f }
xtA env (Alt (DataAlt d) bs rhs) f m
  = m { am_data = am_data m |> xtDNamed d |>> xtG (D (extendCMEs env bs) rhs) f }

fdA :: (a -> b -> b) -> AltMap a -> b -> b
fdA k AM {..} = foldTM k am_deflt
                . foldTM (foldTM k) am_data
                . foldTM (foldTM k) am_lit
