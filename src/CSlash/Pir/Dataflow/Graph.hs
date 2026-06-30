{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module CSlash.Pir.Dataflow.Graph where

import CSlash.Utils.Misc

import CSlash.Pir.Dataflow.Label
import CSlash.Pir.Dataflow.Block

import Data.Kind

type Body s n = Body' s Block n

type Body' s block (n :: Extensibility -> Extensibility -> Type) = s (block n C C)

class NonLocal thing where
  entryLabel :: thing C x -> Label
  successors :: thing e C -> [Label]

instance NonLocal n => NonLocal (Block n) where
  entryLabel (BlockCO f _) = entryLabel f
  entryLabel (BlockCC f _ _) = entryLabel f

  successors (BlockOC _ n) = successors n
  successors (BlockCC _ _ n) = successors n

bodyToBlockList :: Body LabelMap n -> [Block n C C]
bodyToBlockList body = mapElems body

-- ---------------------------------------------------------------------------
-- Graph

type Graph = Graph' LabelMap Block

data Graph' s block (n :: Extensibility -> Extensibility -> Type) e x where
  GNil :: Graph' s block n O O
  GUnit :: block n O O -> Graph' s block n O O
  GMany
    :: MaybeO e (block n O C)
    -> Body' s block n
    -> MaybeO x (block n C O)
    -> Graph' s block n e x

----------------------------------------------------------------

revPostorderFrom
  :: forall block. (NonLocal block)
  => LabelMap (block C C)
  -> Label
  -> [block C C]
revPostorderFrom graph start = go start_worklist setEmpty []
  where
    start_worklist = lookup_for_descend start Nil

    go :: DfsStack (block C C) -> LabelSet -> [block C C] -> [block C C]
    go Nil !_ !result = result
    go (ConsMark block rest) !wip_or_done !result
      = go rest wip_or_done (block : result)
    go (ConsTodo block rest) !wip_or_done !result
      | entryLabel block `setMember` wip_or_done
      = go rest wip_or_done result
      | otherwise
      = let new_worklist = foldr lookup_for_descend (ConsMark block rest) (successors block)
        in go new_worklist (setInsert (entryLabel block) wip_or_done) result

    lookup_for_descend :: Label -> DfsStack (block C C) -> DfsStack (block C C)
    lookup_for_descend label wl
      | Just b <- mapLookup label graph
      = ConsTodo b wl
      | otherwise
      = error $ "Label that doesn't have a block!? " ++ show label

data DfsStack a = ConsTodo a (DfsStack a) | ConsMark a (DfsStack a) | Nil
