module CSlash.Core.Opt.Stats where

import CSlash.Cs.Pass

import CSlash.Core
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

isZeroSimplCount :: SimplCount -> Bool
isZeroSimplCount (VerySimplCount n) = n == 0
isZeroSimplCount SimplCount = panic "isZerosimplcount"

hasDetailedCounts :: SimplCount -> Bool
hasDetailedCounts VerySimplCount{} = False
hasDetailedCounts SimplCount{} = True

doFreeSimplTick  :: Tick -> SimplCount -> SimplCount
doFreeSimplTick tick sc@SimplCount = sc
doFreeSimplTick _ sc = sc

doSimplTick :: Int -> Tick -> SimplCount -> SimplCount
doSimplTick history_size tick sc@SimplCount = panic "doSimplTick"
doSimplTick _ _ (VerySimplCount n) = VerySimplCount (n + 1)

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

simplCountN :: SimplCount -> Int
simplCountN (VerySimplCount n) = n
simplCountN SimplCount = panic "simplcountn"

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
  | EtaExpansion CoreBndr
  | EtaReduction CoreBndr
  | BetaReduction CoreBndr (Maybe (MonoKind Zk))

  | CaseOfCase (Id Zk)
  | KnownBranch (Id Zk)
  | CaseElim (Id Zk)

  | SimplifierDone
