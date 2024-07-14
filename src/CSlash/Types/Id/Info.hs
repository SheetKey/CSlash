module CSlash.Types.Id.Info where

import CSlash.Types.Name
import CSlash.Types.Basic
import CSlash.Core.DataCon
import CSlash.Unit.Module

import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Data.Data ( Data )
import Data.Word

data IdDetails
  = VanillaId
  | DataConWorkId DataCon
  | DataConWrapId DataCon
  | TickBoxOpId TickBoxOp
  | JoinId JoinArity

type TickBoxOpId = Int

data TickBoxOp = TickBox Module {-# UNPACK #-} !TickBoxId

instance Outputable TickBoxOp where
  ppr (TickBox mod n) = text "tixk" <+> ppr (mod, n)
