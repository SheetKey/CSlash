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

instance Functor CoreMapX where
  fmap f CM = CM

instance TrieMap CoreMapX where
  type Key CoreMapX = DeBruijn CoreExpr
  emptyTM = emptyE
  lookupTM = lkE
  alterTM = xtE
  foldTM = fdE
  filterTM = ftE

ftE :: (a -> Bool) -> CoreMapX a -> CoreMapX a
ftE f CM = CM

fdE :: (a -> b -> b) -> CoreMapX a -> b -> b
fdE k m = panic "fdE"

lkE :: DeBruijn CoreExpr -> CoreMapX a -> Maybe a
lkE (D env expr) cm = panic "lkE"

xtE :: DeBruijn CoreExpr -> XT a -> CoreMapX a -> CoreMapX a
xtE = panic "xtE"

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
