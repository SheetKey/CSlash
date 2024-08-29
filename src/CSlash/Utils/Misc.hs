module CSlash.Utils.Misc
  ( module X
  , module CSlash.Utils.Misc
  ) where

import GHC.Utils.Misc as X

import CSlash.Utils.Panic.Plain

-- Combination of foldr and zip. Must be the same length
foldr2 :: (a -> b -> c -> c) -> c -> [a] -> [b] -> c
foldr2 f c = go
  where
    go [] [] = c
    go (a:as) (b:bs) = f a b (go as bs)
    go _ _ = panic "Util: foldr2"
