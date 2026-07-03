module CSlash.Pir.Graph where

import CSlash.Platform.Profile

import CSlash.Pir.BlockId
import CSlash.Pir
-- import GHC.Cmm.CallConv
-- import GHC.Cmm.Switch (SwitchTargets)

import CSlash.Pir.Dataflow.Block
import CSlash.Pir.Dataflow.Graph
import CSlash.Pir.Dataflow.Label
import CSlash.Data.FastString
-- import GHC.Types.ForeignCall
import CSlash.Data.OrdList
-- import GHC.Runtime.Heap.Layout (ByteOff)
import CSlash.Types.Unique.DSM
import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Panic

-----------------------------------------------------------------------------
-- Building Graphs

type PirAGraph = OrdList CgStmt

data CgStmt
  = CgLabel BlockId
  | CgStmt (PirNode O O)
  | CgLast (PirNode O C)
  | CgFork BlockId PirAGraph

---------- AGraph manipulation

(<:>) :: PirAGraph -> PirAGraph -> PirAGraph
(<:>) = appOL

---------- No-ops

mkNop :: PirAGraph
mkNop = nilOL
