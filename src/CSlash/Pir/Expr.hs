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

instance Eq PirExpr -- where
  -- PirLit l1 == PirLit l2 = l1 == l2
  -- PirReg r1 == PirReg r2 == r1 == r2
  -- _ == _ = False

instance OutputableP Platform PirExpr where
  pdoc = pprExpr

data PirLit
  = PirLabel PLabel

instance OutputableP Platform PirLit

instance Outputable PirLit

-- --------------------------------------------------------------------------
-- Pretty-printing expressions
-- --------------------------------------------------------------------------

pprExpr :: Platform -> PirExpr -> SDoc
pprExpr platform e = case e of
  PirLit lit -> pprLit platform lit
  _ -> pprExpr1 platform e

pprExpr1 :: Platform -> PirExpr -> SDoc
-- pprExpr1 platform (PirMachOp op [x, y])
pprExpr1 platform e = pprExpr7 platform e

pprExpr7 :: Platform -> PirExpr -> SDoc
-- pprExpr7 platform (PirMachOp
pprExpr7 platform e = pprExpr8 platform e

pprExpr8 :: Platform -> PirExpr -> SDoc
-- pprExpr8 platform (PirMachOp
pprExpr8 platform e = pprExpr9 platform e

pprExpr9 :: Platform -> PirExpr -> SDoc
pprExpr9 platform e = case e of
  PirLit lit -> pprLit1 platform lit
  PirReg reg -> ppr reg

-- --------------------------------------------------------------------------
-- Pretty-printing literals
--
--  To minimise line noise we adopt the convention that if the literal
--  has the natural machine word size, we do not append the type
-- --------------------------------------------------------------------------

pprLit :: Platform -> PirLit -> SDoc
pprLit platform lit = case lit of
  PirLabel plbl -> pdoc platform plbl

pprLit1 :: Platform -> PirLit -> SDoc
-- pprLit1 platfoorm lit@PirLabelOff{}
pprLit1 platform lit = pprLit platform lit
