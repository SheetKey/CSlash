{-# LANGUAGE MultiParamTypeClasses #-}

module CSlash.Pir.PLabel where

import CSlash.Types.Var.Id.Info
import CSlash.Types.Basic
-- import {-# SOURCE #-} CSlash.Pir.BlockId (BlockId, mkBlockId)
import CSlash.Unit.Types
import CSlash.Types.Name
import CSlash.Types.Unique
import CSlash.Builtin.PrimOps
-- import GHC.Types.CostCentre
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Data.FastString
import CSlash.Platform
import CSlash.Types.Unique.Set
import CSlash.Core.Ppr ( {- instances -} )
import CSlash.Types.SrcLoc

import qualified Data.Semigroup as S

data PLabel
  = IdLabel Name CafInfo IdLabelInfo
  
instance OutputableP Platform PLabel

data IdLabelInfo
  = Function
  | Entry

-- -----------------------------------------------------------------------------
-- Constructing PLabels
-- -----------------------------------------------------------------------------

mkFunctionLabel :: Name -> CafInfo -> PLabel
mkFunctionLabel name c = IdLabel name c Function

-- -----------------------------------------------------------------------------
-- Convert between different kinds of label

toEntryLbl :: Platform -> PLabel -> PLabel
toEntryLbl platform lbl = case lbl of
  IdLabel n c Function -> IdLabel n c Entry
  IdLabel n c Entry -> IdLabel n c Entry

toProcDelimiterLbl :: PLabel -> PLabel
toProcDelimiterLbl lbl = case lbl of
  -- LocalBlockLabel{}
  _ -> lbl
