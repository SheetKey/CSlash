module CSlash.Builtin.Uniques where

import CSlash.Types.Unique
import CSlash.Types.Basic
import CSlash.Data.FastString

isTupleTyConUnique :: Unique -> Maybe Arity
isSumTyConUnique :: Unique -> Maybe Arity

varNSUnique :: Unique
tvNSUnique :: Unique
kvNSUnique :: Unique
tcNSUnique :: Unique
dataNSUnique :: Unique
unknownNSUnique :: Unique
mkRowNSUnique :: FastString -> Unique
