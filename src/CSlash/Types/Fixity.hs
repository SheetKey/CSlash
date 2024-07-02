module CSlash.Types.Fixity ( module X ) where

import GHC.Types.Fixity as X

import CSlash.Utils.Outputable

instance Outputable Fixity where
  ppr (Fixity _ prec dir) = hcat [ppr dir, space, int prec]

instance Outputable FixityDirection where
  ppr InfixL = text "infixl"
  ppr InfixR = text "infixr"
  ppr InfixN = text "infix"
