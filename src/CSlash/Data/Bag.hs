module CSlash.Data.Bag ( module X, module CSlash.Data.Bag ) where

import GHC.Data.Bag as X hiding (pprBag)

import CSlash.Utils.Outputable

instance (Outputable a) => Outputable (Bag a) where
  ppr = pprBag

pprBag :: Outputable a => Bag a -> SDoc
pprBag bag = braces (pprWithCommas ppr (bagToList bag))
