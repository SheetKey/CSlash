module CSlash.Builtin.Uniques where

import {-# SOURCE #-} CSlash.Builtin.Types
import {-# SOURCE #-} CSlash.Core.TyCon
import {-# SOURCE #-} CSlash.Core.DataCon
import CSlash.Types.Var.Id ()
import {-# SOURCE #-} CSlash.Types.Var.Class (varName)
import {-# SOURCE #-} CSlash.Types.Name hiding (varName)
import CSlash.Types.Basic
import CSlash.Types.Unique

import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import CSlash.Utils.Word64 (word64ToInt)

import Data.Bits ((.&.), (.|.), shiftR, shiftL)

knownUniqueName :: Unique -> Maybe Name
knownUniqueName u =
  case tag of
    'z' -> Just $ getSumName n
    '4' -> Just $ getTupleTyConName n
    '7' -> Just $ getTupleDataConName n
    _ -> Nothing
  where
    (tag, n') = unpkUnique u
    n = assert (isValidKnownKeyUnique u) (word64ToInt n')

mkSumTyConUnique :: Arity -> Unique
mkSumTyConUnique arity =
  assertPpr (arity <= 0x3f) (ppr arity) $
  mkUniqueInt 'z' (arity `shiftL` 8 .|. 0xfc)

isSumTyConUnique :: Unique -> Maybe Arity
isSumTyConUnique u =
  case (tag, n .&. 0xfc) of
    ('z', 0xfc) -> Just (word64ToInt n `shiftR` 8)
    _ -> Nothing
  where
    (tag, n) = unpkUnique u

mkSumDataConUnique :: ConTagZ -> Arity -> Unique
mkSumDataConUnique alt arity
  | alt >= arity
  = panic ("mkSumDataConUnique: " ++ show alt ++ " >= " ++ show arity)
  | otherwise
  = mkUniqueInt 'z' (arity `shiftL` 8 + alt `shiftL` 2)

getSumName :: Int -> Name
getSumName n
  | n .&. 0xfc == 0xfc
  = case tag of
      0x0 -> tyConName $ sumTyCon arity
      _   -> pprPanic "getSumName: invalid tag" (ppr tag)
  | tag == 0x0
  = dataConName $ sumDataCon (alt + 1) arity
  | otherwise
  = pprPanic "getUnboxedSumName" (ppr n)
  where
    arity = n `shiftR` 8
    alt = (n .&. 0xfc) `shiftR` 2
    tag = 0x3 .&. n

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

getTupleTyConName :: Int -> Name
getTupleTyConName n =
  case n `divMod` 2 of
    (arity, 0) -> tyConName $ tupleTyCon arity
    _ -> panic "getTupleTyConName"

getTupleDataConName :: Int -> Name
getTupleDataConName n =
  case n `divMod` 3 of
    (arity, 0) -> dataConName $ tupleDataCon arity
    (arity, 1) -> varName $ dataConId $ tupleDataCon arity
    _ -> panic "getTupleDataConName"

mkAlphaTyVarUnique :: Int -> Unique
mkAlphaTyVarUnique i = mkUniqueInt '1' i

mkAlphaKiVarUnique :: Int -> Unique
mkAlphaKiVarUnique i = mkUniqueInt '1' i

mkFunKiVarUnique :: Int -> Unique
mkFunKiVarUnique i = mkUniqueInt '2' i

-- mkPreludeMiscIdUnique
mkWiredInMiscIdUnique :: Int -> Unique
mkWiredInMiscIdUnique i = mkUniqueInt '0' i

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

dataConUnique :: Unique -> Unique
dataConUnique u = incrUnique u
