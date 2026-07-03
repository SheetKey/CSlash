{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DerivingStrategies #-}

module CSlash.Pir.Dataflow.Label where

import CSlash.Utils.Outputable

import CSlash.Types.Unique (Uniquable(..), mkUniqueGrimily)

import CSlash.Data.Word64Set (Word64Set)
import qualified CSlash.Data.Word64Set as S
import CSlash.Data.Word64Map.Strict (Word64Map)
import qualified CSlash.Data.Word64Map.Strict as M
import CSlash.Data.TrieMap

import Data.Word (Word64)
import Data.List (foldl1')

-----------------------------------------------------------------------------
--              Label
-----------------------------------------------------------------------------

newtype Label = Label { lblToUnique :: Word64 }
  deriving newtype (Eq, Ord)

instance Show Label where
  show (Label n) = "L" ++ show n

instance Uniquable Label where
  getUnique label = mkUniqueGrimily (lblToUnique label)

instance Outputable Label where
  ppr label = ppr (getUnique label)

instance OutputableP env Label where
  pdoc _ l = ppr l

-----------------------------------------------------------------------------
-- LabelSet

newtype LabelSet = LS Word64Set
  deriving newtype (Eq, Ord, Show, Monoid, Semigroup)

setNull :: LabelSet -> Bool
setNull (LS s) = S.null s

setSize :: LabelSet -> Int
setSize (LS s) = S.size s

setMember :: Label -> LabelSet -> Bool
setMember (Label k) (LS s) = S.member k s

setEmpty :: LabelSet
setEmpty = LS S.empty

setSingleton :: Label -> LabelSet
setSingleton (Label k) = LS (S.singleton k)

setInsert :: Label -> LabelSet -> LabelSet
setInsert (Label k) (LS s) = LS (S.insert k s)

setDelete :: Label -> LabelSet -> LabelSet
setDelete (Label k) (LS s) = LS (S.delete k s)

setUnion :: LabelSet -> LabelSet -> LabelSet
setUnion (LS x) (LS y) = LS (S.union x y)

{-# INLINE setUnions #-}
setUnions :: [LabelSet] -> LabelSet
setUnions [] = setEmpty
setUnions sets = foldl1' setUnion sets

setDifference :: LabelSet -> LabelSet -> LabelSet
setDifference (LS x) (LS y) = LS (S.difference x y)

setIntersection :: LabelSet -> LabelSet -> LabelSet
setIntersection (LS x) (LS y) = LS (S.intersection x y)

setIsSubsetOf :: LabelSet -> LabelSet -> Bool
setIsSubsetOf (LS x) (LS y) = S.isSubsetOf x y

-----------------------------------------------------------------------------
-- LabelMap

newtype LabelMap v = LM (Word64Map v)
  deriving newtype (Eq, Ord, Show, Functor, Foldable)
  deriving stock Traversable

mapNull :: LabelMap a -> Bool
mapNull (LM m) = M.null m

{-# INLINE mapSize #-}
mapSize :: LabelMap a -> Int
mapSize (LM m) = M.size m

mapMember :: Label -> LabelMap a -> Bool
mapMember (Label k) (LM m) = M.member k m

mapLookup :: Label -> LabelMap a -> Maybe a
mapLookup (Label k) (LM m) = M.lookup k m

mapFindWithDefault :: a -> Label -> LabelMap a -> a
mapFindWithDefault def (Label k) (LM m) = M.findWithDefault def k m

mapEmpty :: LabelMap v
mapEmpty = LM M.empty

mapSingleton :: Label -> v -> LabelMap v
mapSingleton (Label k) v = LM (M.singleton k v)

mapInsert :: Label -> v -> LabelMap v -> LabelMap v
mapInsert (Label k) v (LM m) = LM (M.insert k v m)

mapInsertWith :: (v -> v -> v) -> Label -> v -> LabelMap v -> LabelMap v
mapInsertWith f (Label k) v (LM m) = LM (M.insertWith f k v m)

mapDelete :: Label -> LabelMap v -> LabelMap v
mapDelete (Label k) (LM m) = LM (M.delete k m)

mapAlter :: (Maybe v -> Maybe v) -> Label -> LabelMap v -> LabelMap v
mapAlter f (Label k) (LM m) = LM (M.alter f k m)

mapAdjust :: (v -> v) -> Label -> LabelMap v -> LabelMap v
mapAdjust f (Label k) (LM m) = LM (M.adjust f k m)

mapUnion :: LabelMap v -> LabelMap v -> LabelMap v
mapUnion (LM x) (LM y) = LM (M.union x y)

{-# INLINE mapUnions #-}
mapUnions :: [LabelMap a] -> LabelMap a
mapUnions [] = mapEmpty
mapUnions maps = foldl1' mapUnion maps

{-# INLINEABLE mapFilter #-}
mapFilter :: (v -> Bool) -> LabelMap v -> LabelMap v
mapFilter f (LM m) = LM (M.filter f m)

{-# INLINE mapElems #-}
mapElems :: LabelMap a -> [a]
mapElems (LM m) = M.elems m

{-# INLINE mapFromList #-}
mapFromList :: [(Label, v)] -> LabelMap v
mapFromList assocs = LM (M.fromList [(lblToUnique k, v) | (k, v) <- assocs])
