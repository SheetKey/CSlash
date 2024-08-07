module CSlash.Types.Unique.Set ( module X ) where

import GHC.Types.Unique.Set as X hiding (pprUniqSet)

import CSlash.Utils.Outputable

instance Outputable a => Outputable (UniqSet a) where
  ppr = pprUniqSet ppr

pprUniqSet :: (a -> SDoc) -> UniqSet a -> SDoc
pprUniqSet f = braces . pprWithCommas f . nonDetEltsUniqSet
