{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}

module CSlash.Types.Unique (
        Unique, Uniquable(..),
        uNIQUE_BITS,

        hasKey,

        pprUniqueAlways,

        mkTag,
        mkUniqueGrimily,
        mkUniqueIntGrimily,
        getKey,
        mkUnique, unpkUnique,
        mkUniqueInt,
        eqUnique, ltUnique,
        incrUnique, stepUnique,

        newTagUnique,
        nonDetCmpUnique,
        isValidKnownKeyUnique,

        mkLocalUnique, minLocalUnique, maxLocalUnique,
    ) where

import CSlash.Utils.Outputable
import CSlash.Utils.Word64 (intToWord64, word64ToInt)

import CSlash.Exts (indexCharOffAddr#, Char(..), Int(..))

import Data.Word ( Word64 )

import GHC.Types.Unique hiding (pprUniqueAlways)

showUnique :: Unique -> String
showUnique uniq
  = case unpkUnique uniq of
      (tag, u) -> tag : w64ToBase62 u

pprUniqueAlways :: IsLine doc => Unique -> doc
pprUniqueAlways u
  = text (showUnique u)
{-# SPECIALIZE pprUniqueAlways :: Unique -> SDoc #-}
{-# SPECIALIZE pprUniqueAlways :: Unique -> HLine #-} 

instance Outputable Unique where
    ppr = pprUniqueAlways

w64ToBase62 :: Word64 -> String
w64ToBase62 n_ = go n_ ""
  where
    go n cs | n < 62
            = let !c = chooseChar62 (word64ToInt n) in c : cs
            | otherwise
            = go q (c : cs) where (!q, r) = quotRem n 62
                                  !c = chooseChar62 (word64ToInt r)

    chooseChar62 :: Int -> Char
    {-# INLINE chooseChar62 #-}
    chooseChar62 (I# n) = C# (indexCharOffAddr# chars62 n)
    chars62 = "0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"#
