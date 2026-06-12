{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

module CSlash.Data.TrieMap
  ( module CSlash.Data.TrieMap
  , module X
  ) where

import GHC.Data.TrieMap as X

data EitherMap m1 m2 a = EM { em_left :: m1 a, em_right :: m2 a }

instance (Functor m1, Functor m2)  => Functor (EitherMap m1 m2) where
  fmap f EM {..} = EM
    { em_left = fmap f em_left
    , em_right = fmap f em_right }

instance (TrieMap m1, TrieMap m2) => TrieMap (EitherMap m1 m2) where
  type Key (EitherMap m1 m2) = Either (Key m1) (Key m2)
  emptyTM = EM emptyTM emptyTM
  lookupTM = lkEither lookupTM lookupTM
  alterTM = xtEither alterTM alterTM
  foldTM = fdEither
  filterTM = ftEither

instance (TrieMap m1, TrieMap m2) => Foldable (EitherMap m1 m2) where
  foldMap = foldMapTM

lkEither
  :: (forall b. k1 -> m1 b -> Maybe b)
  -> (forall b. k2 -> m2 b -> Maybe b)
  -> Either k1 k2 -> EitherMap m1 m2 a -> Maybe a
lkEither lk _ (Left x) = em_left >.> lk x
lkEither _ lk (Right x) = em_right >.> lk x

xtEither
  :: (forall b. k1 -> XT b -> m1 b -> m1 b)
  -> (forall b. k2 -> XT b -> m2 b -> m2 b)
  -> Either k1 k2 -> XT a -> EitherMap m1 m2 a -> EitherMap m1 m2 a
xtEither tr _ (Left x) f m = m { em_left = em_left m |> tr x f }
xtEither _ tr (Right x) f m = m { em_right = em_right m |> tr x f }

fdEither :: (TrieMap m1, TrieMap m2) => (a -> b -> b) -> EitherMap m1 m2 a -> b -> b
fdEither k m = foldTM k (em_left m)
               . foldTM k (em_right m)

ftEither :: (TrieMap m1, TrieMap m2) => (a -> Bool) -> EitherMap m1 m2 a -> EitherMap m1 m2 a
ftEither f EM {..} = EM
  { em_left = filterTM f em_left
  , em_right = filterTM f em_right }
