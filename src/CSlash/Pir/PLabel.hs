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
  
instance OutputableP Platform PLabel
