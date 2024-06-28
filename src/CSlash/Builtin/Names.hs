import CSlash.Builtin.Names
  ( Unique, Uniquable(..), hasKey,
    module CSlash.Builtin.Names
  ) where

import CSlash.Data.List.Infinite (Infinite (..))
import qualified CSlash.Data.List.Infinite as Inf

allNameStrings :: Infinite String
-- Infinite list of a,b,c...z, aa, ab, ac, ... etc
allNameStrings = Inf.allListsOf ['a'..'z']

allNameStringList :: [String]
-- Infinite list of a,b,c...z, aa, ab, ac, ... etc
allNameStringList = Inf.toList allNameStrings
