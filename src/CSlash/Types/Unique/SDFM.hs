module CSlash.Types.Unique.SDFM
  ( module X
  ) where

import GHC.Types.Unique.SDFM as X

import CSlash.Utils.Outputable

instance (Outputable a, Outputable b) => Outputable (UniqSDFM a b)
