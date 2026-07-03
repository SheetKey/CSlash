module CSlash.StgToPir.Sequel where

import CSlash.Cs.Pass

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
  { sli_id :: !(Id Zk)
  , sli_arity :: !RepArity
  , sli_registers :: ![LocalReg]
  , sli_header_block :: !BlockId
  }
