{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module CSlash.Core.Map.Expr where

import CSlash.Data.TrieMap
import CSlash.Core.Map.Type
import CSlash.Core
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
  (==) = panic "eqDeBruijnExpr"

instance Outputable a => Outputable (CoreMap a)

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
