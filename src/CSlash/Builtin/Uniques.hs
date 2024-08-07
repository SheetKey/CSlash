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

mkTupleDataConUnique :: Arity -> Unique
mkTupleDataConUnique a = mkUniqueInt '7' (3*a)

mkTupleTyConUnique :: Arity -> Unique
mkTupleTyConUnique a = mkUniqueInt '4' (2*a)

isTupleTyConUnique :: Unique -> Maybe Arity
isTupleTyConUnique u =
  case (tag, i) of
    ('4', 0) -> Just arity
    _ -> Nothing
  where
    (tag, n) = unpkUnique u
    (arity', i) = quotRem n 2
    arity = word64ToInt arity'

isTupleDataConLikeUnique :: Unique -> Maybe Arity
isTupleDataConLikeUnique u =
  case tag of
    '7' -> Just arity
    _ -> Nothing
  where
    (tag,   n) = unpkUnique u
    (arity', _) = quotRem n 3
    arity = word64ToInt arity'

mkAlphaTyVarUnique :: Int -> Unique
mkAlphaTyVarUnique i = mkUniqueInt '1' i

varNSUnique :: Unique
varNSUnique = mkUnique 'i' 0

tvNSUnique :: Unique
tvNSUnique = mkUnique 'v' 0

kvNSUnique :: Unique
kvNSUnique = mkUnique 'k' 0

tcNSUnique :: Unique
tcNSUnique = mkUnique 'c' 0

dataNSUnique :: Unique
dataNSUnique = mkUnique 'd' 0

unknownNSUnique :: Unique
unknownNSUnique = mkUnique 'u' 0

-- renamed from mkPreludeTyConUnique
mkWiredInTyConUnique :: Int -> Unique
mkWiredInTyConUnique i = mkUniqueInt '3' (2*i)

mkWiredInDataConUnique :: Int -> Unique
mkWiredInDataConUnique i = mkUniqueInt '6' (3*i)

dataConWorkerUnique :: Unique -> Unique
dataConWorkerUnique u = incrUnique u
