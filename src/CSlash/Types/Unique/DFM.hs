module CSlash.Types.Unique.DFM
  ( module X
  , module CSlash.Types.Unique.DFM
  ) where

import GHC.Types.Unique.DFM as X hiding (pprUDFM)

import CSlash.Utils.Outputable

pprUDFM :: UniqDFM key a -> ([a] -> SDoc) -> SDoc
pprUDFM ufm pp = pp (eltsUDFM ufm)
