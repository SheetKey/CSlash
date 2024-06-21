module CSlash.Builtin.Uniques where

import CSlash.Types.Unique

varNSUnique :: Unique
varNSUnique = mkUnique 'i' 0

tvNSUnique :: Unique
tvNSUnique = mkUnique 'v' 0

kvNSUnique :: Unique
kvNSUnique = mkUnique 'k' 0
