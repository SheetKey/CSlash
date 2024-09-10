module CSlash.Types.Unique.DSet (module X) where

import GHC.Types.Unique.DSet as X hiding (pprUniqDSet)

import CSlash.Utils.Outputable

instance Outputable a => Outputable (UniqDSet a) where
  ppr = pprUniqDSet ppr

pprUniqDSet :: (a -> SDoc) -> UniqDSet a -> SDoc
pprUniqDSet f = braces . pprWithCommas f . uniqDSetToList
