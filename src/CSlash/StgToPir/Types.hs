module CSlash.StgToPir.Types where

import CSlash.Cs.Pass

import CSlash.Core.DataCon

-- import GHC.Runtime.Heap.Layout

import CSlash.Types.Basic
-- import GHC.Types.ForeignStubs
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set

import CSlash.Utils.Outputable

data PirCgInfos = PirCgInfos

--------------------------------------------------------------------------------
--                LambdaFormInfo
--------------------------------------------------------------------------------

data LambdaFormInfo
  = LFReEntrant
    !TopLevelFlag
    !RepArity
    !Bool
    -- !ArgDescr
  | LFCon
    !(DataCon Zk)
  | LFUnknown
    !Bool
