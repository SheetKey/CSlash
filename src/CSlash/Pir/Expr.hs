{-# LANGUAGE MultiParamTypeClasses #-}

module CSlash.Pir.Expr
  ( module CSlash.Pir.Expr
  , LocalReg(..)
  ) where

import CSlash.Platform
-- import CSlash.Pir.BlockId
import CSlash.Pir.PLabel
-- import CSlash.Pir.MachOp
import CSlash.Pir.Type
import CSlash.Pir.Reg
import CSlash.Utils.Panic (panic)
import CSlash.Utils.Outputable

import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import Numeric ( fromRat )

import CSlash.Types.Basic (Alignment, mkAlignment, alignmentOf)

-----------------------------------------------------------------------------
--              PirExpr
-- An expression.  Expressions have no side effects.
-----------------------------------------------------------------------------

data PirExpr
  = PirLit !PirLit

  | PirReg {-# UNPACK #-} !LocalReg

instance OutputableP Platform PirExpr

data PirLit
  = PirLabel PLabel

instance OutputableP Platform PirLit

instance Outputable PirLit
