module CSlash.Types.Unique.Map ( module X ) where

import GHC.Types.Unique.Map as X

import CSlash.Types.Unique.FM (nonDetEltsUFM)

import CSlash.Utils.Outputable

instance (Outputable k, Outputable a) => Outputable (UniqMap k a) where
  ppr (UniqMap m) =
    brackets $ fsep $ punctuate comma $
    [ ppr k <+> text "->" <+> ppr v
    | (k, v) <- nonDetEltsUFM m ]
