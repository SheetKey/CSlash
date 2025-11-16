module CSlash.Data.Pair (module X) where

import GHC.Data.Pair as X

import CSlash.Utils.Outputable

instance Outputable a => Outputable (Pair a) where
  ppr (Pair a b) = ppr a <+> char '~' <+> ppr b
