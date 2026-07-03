{-# LANGUAGE BangPatterns #-}

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

flattenPirAGraph :: BlockId -> PirAGraph -> DPirGraph
flattenPirAGraph id stmts_t =
  PirGraph { g_entry = id
           , g_graph = GMany NothingO body NothingO }
  where
    body = DWrap [(entryLabel b, b) | b <- flatten id stmts_t [] ]

    flatten :: Label -> PirAGraph -> [Block PirNode C C] -> [Block PirNode C C]
    flatten id g blocks = flatten1 (fromOL g) block' blocks
      where !block' = blockJoinHead (PirEntry id) emptyBlock

    flatten0 :: [CgStmt] -> [Block PirNode C C] -> [Block PirNode C C]
    flatten0 [] blocks = blocks
    flatten0 (CgLabel id : stmts) blocks
      = flatten1 stmts block blocks
        where !block = blockJoinHead (PirEntry id) emptyBlock
    flatten0 (CgFork fork_id stmts_t : rest) blocks
      = flatten fork_id stmts_t $ flatten0 rest blocks
    flatten0 (CgLast _ : stmts) blocks = flatten0 stmts blocks
    flatten0 (CgStmt _ : stmts) blocks = flatten0 stmts blocks

    flatten1 :: [CgStmt] -> Block PirNode C O -> [Block PirNode C C] -> [Block PirNode C C]
    flatten1 [] block blocks = blockJoinTail block (PirBranch (entryLabel block)) : blocks
    flatten1 (CgLast stmt : stmts) block blocks
      = block' : flatten0 stmts blocks
      where !block' = blockJoinTail block stmt
    flatten1 (CgStmt stmt : stmts) block blocks
      = flatten1 stmts block' blocks
      where !block' = blockSnoc block stmt
    flatten1 (CgFork fork_id stmts_t : rest) block blocks
      = flatten fork_id stmts_t $ flatten1 rest block blocks
    flatten1 (CgLabel id : stmts) block blocks
      = blockJoinTail block (PirBranch id) :
        flatten1 stmts (blockJoinHead (PirEntry id) emptyBlock) blocks

---------- AGraph manipulation

(<:>) :: PirAGraph -> PirAGraph -> PirAGraph
(<:>) = appOL

labelAGraph :: BlockId -> PirAGraph -> DPirGraph
labelAGraph lbl ag = flattenPirAGraph lbl ag

---------- No-ops

mkNop :: PirAGraph
mkNop = nilOL
