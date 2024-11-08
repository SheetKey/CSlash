module CSlash.Data.OrdList ( module X ) where

import GHC.Data.OrdList as X

import CSlash.Utils.Outputable

instance Outputable a => Outputable (OrdList a) where
  ppr ol = ppr (fromOL ol)
