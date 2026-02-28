module CSlash.Data.List.SetOps
  ( module X
  , module CSlash.Data.List.SetOps
  ) where

import GHC.Data.List.SetOps as X hiding (getNth)

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic

getNth :: Outputable a => [a] -> Int -> a
getNth xs n = assertPpr (xs `lengthExceeds` n) (ppr n $$ ppr xs) $ xs !! n
