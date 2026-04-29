module CSlash.Core.Opt.Stats where

import CSlash.Cs.Pass

import CSlash.Types.Var
import CSlash.Types.Error
import CSlash.Core.Kind (MonoKind)

import CSlash.Utils.Outputable as Outputable

import CSlash.Data.FastString

import Data.List (sortOn)
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Ord
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Map.Strict as MapStrict
import CSlash.Utils.Panic

data SimplCount
  = VerySimplCount !Int
  | SimplCount
    -- { ticks :: !Int
    -- , details :: !TickCounts
    -- , n_log :: !Int
    -- , log1 :: [Tick]
    -- , log2 :: [Tick]
    -- }

-- type TickCounts = Map Tick Int

pprSimplCount :: SimplCount -> SDoc
pprSimplCount = panic "pprSimplCount"

zeroSimplCount :: Bool -> SimplCount
zeroSimplCount dump_simpl_stats
  | dump_simpl_stats
  = SimplCount
  | otherwise
  = VerySimplCount 0

plusSimplCount :: SimplCount -> SimplCount -> SimplCount 
plusSimplCount SimplCount SimplCount = SimplCount
plusSimplCount (VerySimplCount n) (VerySimplCount m) = VerySimplCount (n + m)
plusSimplCount lhr rhs =
  panic "plusSimplCount"

data Tick
  = PreInlineUnconditionally (Id Zk)
  | PostInlineUnconditionally (Id Zk)

  | UnfoldingDone (Id Zk)
  | RuleFired FastString

  | LetFloatFromLet
  | EtaExpancion (Id Zk)
  | EtaReduction (Id Zk)
  | BetaReduction (Id Zk) (Maybe (MonoKind Zk))

  | CaseOfCase (Id Zk)
  | KnownBranch (Id Zk)
  | SimplifierDone
