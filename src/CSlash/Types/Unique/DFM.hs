module CSlash.Types.Unique.DFM
  ( module X
  , module CSlash.Types.Unique.DFM
  ) where

import GHC.Types.Unique.DFM as X hiding (pprUniqDFM, pprUDFM)
import CSlash.Types.Unique ()
import CSlash.Utils.Outputable

instance Outputable a => Outputable (UniqDFM key a) where
  ppr = pprUniqDFM ppr

pprUniqDFM :: (a -> SDoc) -> UniqDFM key a -> SDoc
pprUniqDFM ppr_elt ufm
  = brackets $ fsep $ punctuate comma
    $ [ ppr uq <+> text ":->" <+> ppr_elt elt
      | (uq, elt) <- udfmToList ufm ]

pprUDFM :: UniqDFM key a -> ([a] -> SDoc) -> SDoc
pprUDFM ufm pp = pp (eltsUDFM ufm)
