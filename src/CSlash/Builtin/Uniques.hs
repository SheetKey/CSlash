module CSlash.Builtin.Uniques where

import CSlash.Types.Basic
import CSlash.Types.Unique

import CSlash.Utils.Word64 (word64ToInt)

import Data.Bits ((.&.), shiftR)

isSumTyConUnique :: Unique -> Maybe Arity
isSumTyConUnique u =
  case (tag, n .&. 0xfc) of
    ('z', 0xfc) -> Just (word64ToInt n `shiftR` 8)
    _ -> Nothing
  where
    (tag, n) = unpkUnique u

isTupleTyConUnique :: Unique -> Maybe Arity
isTupleTyConUnique u =
  case (tag, i) of
    ('4', 0) -> Just arity
    _ -> Nothing
  where
    (tag, n) = unpkUnique u
    (arity', i) = quotRem n 2
    arity = word64ToInt arity'

varNSUnique :: Unique
varNSUnique = mkUnique 'i' 0

tvNSUnique :: Unique
tvNSUnique = mkUnique 'v' 0

kvNSUnique :: Unique
kvNSUnique = mkUnique 'k' 0
