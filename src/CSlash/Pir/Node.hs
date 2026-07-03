{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GADTs #-}

module CSlash.Pir.Node where

import Prelude hiding ((<>))

import CSlash.Pir.PLabel
import CSlash.Pir.Expr
-- import GHC.Cmm.Switch
import CSlash.Data.FastString
import CSlash.Data.Pair
-- import GHC.Types.ForeignCall
import CSlash.Utils.Outputable
-- import GHC.Runtime.Heap.Layout
-- import GHC.Types.Tickish (CmmTickish)
import qualified CSlash.Types.Unique as U
import CSlash.Types.Basic (FunctionOrData(..))

import CSlash.Platform
import CSlash.Pir.Dataflow.Block
import CSlash.Pir.Dataflow.Graph
import CSlash.Pir.Dataflow.Label
import Data.Foldable (toList)
import Data.Functor.Classes (liftCompare)
import Data.Maybe
import Data.List (tails,sortBy)
import CSlash.Types.Unique (nonDetCmpUnique)
import CSlash.Utils.Constants (debugIsOn)

data PirNode e x where
  PirEntry :: {-# UNPACK #-} !Label -> PirNode C O

  PirBranch :: {-# UNPACK #-} !Label -> PirNode O C

instance OutputableP Platform (PirNode e x) where
  pdoc = pprNode

pprNode :: Platform -> PirNode e x -> SDoc
pprNode platform node = pp_node <+> pp_debug
  where
    pp_node :: SDoc
    pp_node = case node of
      PirEntry id -> (sdocOption sdocSuppressUniques $ \cond ->
                         if cond then text "_lbl_" else ppr id)
                     <> colon

      PirBranch ident -> text "goto" <+> ppr ident <> semi

    pp_debug :: SDoc
    pp_debug = if not debugIsOn then empty else
      case node of
        PirEntry{} -> empty
        PirBranch{} -> text "  // PirBranch"

instance OutputableP Platform (Block PirNode C C) where
    pdoc = pprBlock
instance OutputableP Platform (Block PirNode C O) where
    pdoc = pprBlock
instance OutputableP Platform (Block PirNode O C) where
    pdoc = pprBlock
instance OutputableP Platform (Block PirNode O O) where
    pdoc = pprBlock

instance OutputableP Platform (Graph PirNode e x) where
    pdoc = pprGraph

pprBlock
  :: IndexedCO x SDoc SDoc ~ SDoc
  => Platform -> Block PirNode e x -> IndexedCO e SDoc SDoc
pprBlock platform block
  = foldBlockNodesB3 ( ($$) . pdoc platform
                     , ($$) . (nest 4) . pdoc platform
                     , ($$) . (nest 4) . pdoc platform ) block empty

pprGraph :: Platform -> Graph PirNode e x -> SDoc
pprGraph platform graph = case graph of
  GNil -> empty
  GUnit block -> pdoc platform block
  GMany entry body exit ->
    text "{" $$ nest 2 (pprMaybeO entry
                         $$ (vcat $ map (pdoc platform) $ bodyToBlockList body)
                         $$ pprMaybeO exit)
    $$ text "}"
  where
    pprMaybeO
      :: OutputableP Platform (Block PirNode e x)
      => MaybeO ex (Block PirNode e x)
      -> SDoc
    pprMaybeO NothingO = empty
    pprMaybeO (JustO block) = pdoc platform block

---------------------------------------------
-- Eq instance

deriving instance Eq (PirNode e x)

----------------------------------------------
-- NonLocal instances

instance NonLocal PirNode where
  entryLabel (PirEntry l) = l

--------------------------------------------------
-- Various helper types

type PirFormals = [PirFormal]
type PirFormal = LocalReg
