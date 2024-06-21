{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
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

-- #include "Unique.h"
#define UNIQUE_TAG_BITS 8

import CSlash.Data.FastString
import CSlash.Utils.Outputable
import CSlash.Utils.Word64 (intToWord64, word64ToInt)

import CSlash.Exts (indexCharOffAddr#, Char(..), Int(..))

import Data.Word ( Word64 )
import Data.Char ( chr, ord )
import Data.Bits ( shiftL, shiftR, (.&.), (.|.) )

import Language.Haskell.Syntax.Module.Name

newtype Unique = MkUnique Word64

{-# INLINE uNIQUE_BITS #-}
uNIQUE_BITS :: Int
uNIQUE_BITS = 64 - UNIQUE_TAG_BITS

unpkUnique      :: Unique -> (Char, Word64)

mkUniqueGrimily :: Word64 -> Unique        
getKey          :: Unique -> Word64        

incrUnique   :: Unique -> Unique
stepUnique   :: Unique -> Word64 -> Unique
newTagUnique :: Unique -> Char -> Unique

mkUniqueGrimily = MkUnique

{-# INLINE getKey #-}
getKey (MkUnique x) = x

incrUnique (MkUnique i) = MkUnique (i + 1)
stepUnique (MkUnique i) n = MkUnique (i + n)

mkLocalUnique :: Word64 -> Unique
mkLocalUnique i = mkUnique 'X' i

minLocalUnique :: Unique
minLocalUnique = mkLocalUnique 0

maxLocalUnique :: Unique
maxLocalUnique = mkLocalUnique uniqueMask

newTagUnique u c = mkUnique c i where (_,i) = unpkUnique u

uniqueMask :: Word64
uniqueMask = (1 `shiftL` uNIQUE_BITS) - 1

mkTag :: Char -> Word64
mkTag c = intToWord64 (ord c) `shiftL` uNIQUE_BITS

mkUnique :: Char -> Word64 -> Unique
mkUnique c i
  = MkUnique (tag .|. bits)
  where
    tag  = mkTag c
    bits = i .&. uniqueMask

mkUniqueInt :: Char -> Int -> Unique
mkUniqueInt c i = mkUnique c (intToWord64 i)

mkUniqueIntGrimily :: Int -> Unique
mkUniqueIntGrimily = MkUnique . intToWord64

unpkUnique (MkUnique u)
  = let tag = chr (word64ToInt (u `shiftR` uNIQUE_BITS))
        i = u .&. uniqueMask
    in (tag, i)

isValidKnownKeyUnique :: Unique -> Bool
isValidKnownKeyUnique u =
    case unpkUnique u of
      (c, x) -> ord c < 0xff && x <= (1 `shiftL` 22)

class Uniquable a where
    getUnique :: a -> Unique

hasKey          :: Uniquable a => a -> Unique -> Bool
x `hasKey` k    = getUnique x == k

instance Uniquable FastString where
 getUnique fs = mkUniqueIntGrimily (uniqueOfFS fs)

instance Uniquable Int where
  getUnique i = mkUniqueIntGrimily i

instance Uniquable ModuleName where
  getUnique (ModuleName nm) = getUnique nm

eqUnique :: Unique -> Unique -> Bool
eqUnique (MkUnique u1) (MkUnique u2) = u1 == u2

ltUnique :: Unique -> Unique -> Bool
ltUnique (MkUnique u1) (MkUnique u2) = u1 < u2

nonDetCmpUnique :: Unique -> Unique -> Ordering
nonDetCmpUnique (MkUnique u1) (MkUnique u2)
  = if u1 == u2 then EQ else if u1 < u2 then LT else GT

instance Eq Unique where
    a == b = eqUnique a b
    a /= b = not (eqUnique a b)

instance Uniquable Unique where
    getUnique u = u

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

instance Show Unique where
    show uniq = showUnique uniq

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
