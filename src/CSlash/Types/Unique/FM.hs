module CSlash.Types.Unique.FM
  ( module X
  , pprUniqFM, pprUFM
  ) where

import GHC.Types.Unique.FM as X hiding (pprUniqFM, pprUFM)

import CSlash.Types.Unique () -- Unique outputable instance

import CSlash.Utils.Outputable

instance Outputable a => Outputable (UniqFM key a) where
  ppr ufm = pprUniqFM ppr ufm

pprUniqFM :: (a -> SDoc) -> UniqFM key a -> SDoc
pprUniqFM ppr_elt ufm
  = brackets $ fsep $ punctuate comma $
    [ ppr uq <+> text ":->" <+> ppr_elt elt
    | (uq, elt) <- nonDetUFMToList ufm ]

pprUFM :: UniqFM key a -> ([a] -> SDoc) -> SDoc
pprUFM ufm pp = pp (nonDetEltsUFM ufm)
