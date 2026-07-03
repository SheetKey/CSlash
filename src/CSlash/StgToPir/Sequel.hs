module CSlash.StgToPir.Sequel where

import CSlash.Pir.BlockId
import CSlash.Pir

import CSlash.Types.Var.Id
import CSlash.Types.Basic (RepArity)
import CSlash.Utils.Outputable

data Sequel
  = Return

instance Outputable Sequel where
  ppr Return = text "Return"

data SelfLoopInfo = MkSelfLoopInfo
