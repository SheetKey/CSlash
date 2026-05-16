module CSlash.Core.Opt.Stats where

import CSlash.Cs.Pass

import CSlash.Core
import CSlash.Core.Ppr ()
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

getVerboseSimplStats :: (Bool -> SDoc) -> SDoc
getVerboseSimplStats = getPprDebug

isZeroSimplCount :: SimplCount -> Bool
isZeroSimplCount (VerySimplCount n) = n == 0
isZeroSimplCount SimplCount{ ticks = n } = n == 0

hasDetailedCounts :: SimplCount -> Bool
hasDetailedCounts VerySimplCount{} = False
hasDetailedCounts SimplCount{} = True

doFreeSimplTick  :: Tick -> SimplCount -> SimplCount
doFreeSimplTick tick sc@SimplCount{ details = dts }
  = sc { details = dts `addTick` tick }
doFreeSimplTick _ sc = sc

doSimplTick :: Int -> Tick -> SimplCount -> SimplCount
doSimplTick history_size tick sc@SimplCount{ ticks = tks, details = dts, n_log = nl, log1 = l1 }
  | nl >= history_size = sc1 { n_log = 1, log1 = [tick], log2 = l1 }
  | otherwise = sc1 { n_log = nl + 1, log1 = tick : l1 }
  where
    sc1 = sc { ticks = tks + 1, details = dts `addTick` tick }
doSimplTick _ _ (VerySimplCount n) = VerySimplCount (n + 1)

addTick :: TickCounts -> Tick -> TickCounts
addTick fm tick = MapStrict.insertWith (+) tick 1 fm

data SimplCount
  = VerySimplCount !Int
  | SimplCount
    { ticks :: !Int
    , details :: !TickCounts
    , n_log :: !Int
    , log1 :: [Tick]
    , log2 :: [Tick]
    }

type TickCounts = Map Tick Int

simplCountN :: SimplCount -> Int
simplCountN (VerySimplCount n) = n
simplCountN SimplCount{ ticks = n } = n

pprSimplCount :: SimplCount -> SDoc
pprSimplCount (VerySimplCount n) = text "Total ticks:" <+> int n
pprSimplCount SimplCount{ ticks = tks, details = dts, log1 = l1, log2 = l2 }
  = vcat [ text "Total ticks:    " <+> int tks
         , blankLine
         , pprTickCounts dts
         , getVerboseSimplStats $ \dbg -> if dbg
           then vcat [ blankLine
                     , text "Log (most recent first)"
                     , nest 4 (vcat (map ppr l1) $$ vcat (map ppr l2)) ]
           else Outputable.empty
         ]

zeroSimplCount :: Bool -> SimplCount
zeroSimplCount dump_simpl_stats
  | dump_simpl_stats
  = SimplCount { ticks = 0, details = Map.empty
               , n_log = 0, log1 = [], log2 = [] }
  | otherwise
  = VerySimplCount 0

plusSimplCount :: SimplCount -> SimplCount -> SimplCount 
plusSimplCount sc1@SimplCount{ ticks = tks1, details = dts1 }
               sc2@SimplCount{ ticks = tks2, details = dts2 }
  = log_base { ticks = tks1 + tks2
             , details = MapStrict.unionWith (+) dts1 dts2 }
  where
    log_base | null (log1 sc2) = sc1
             | null (log2 sc2) = sc2 { log2 = log1 sc1 }
             | otherwise = sc2
plusSimplCount (VerySimplCount n) (VerySimplCount m) = VerySimplCount (n + m)
plusSimplCount lhr rhs = panic "plusSimplCount"

pprTickCounts :: Map Tick Int -> SDoc
pprTickCounts counts
  = vcat (map pprTickGroup groups)
  where
    groups :: [NonEmpty (Tick, Int)]
    groups = NE.groupWith (tickToTag . fst) (Map.toList counts)

pprTickGroup :: NonEmpty (Tick, Int) -> SDoc
pprTickGroup group@((tick1, _) :| _)
  = hang (int (sum (fmap snd group)) <+> pprTickType tick1)
    2 (vcat [ int n <+> pprTickCts tick
            | (tick, n) <- sortOn (Down . snd) (NE.toList group) ])

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

instance Outputable Tick where
  ppr tick = pprTickType tick <+> pprTickCts tick

instance Eq Tick where
  a == b = case a `cmpTick` b of
             EQ -> True
             _ -> False

instance Ord Tick where
  compare = cmpTick

tickToTag :: Tick -> Int
tickToTag PreInlineUnconditionally{} = 0
tickToTag PostInlineUnconditionally{} = 1
tickToTag UnfoldingDone{} = 3
tickToTag RuleFired{} = 3     
tickToTag LetFloatFromLet = 4          
tickToTag EtaExpansion{} = 5    
tickToTag EtaReduction{} = 6    
tickToTag BetaReduction{} = 7
tickToTag CaseOfCase{} = 8      
tickToTag KnownBranch{} = 9
tickToTag CaseElim{} = 11        
tickToTag SimplifierDone = 16          

pprTickType :: Tick -> SDoc
pprTickType PreInlineUnconditionally{} = text "PreInlineUnconditionally"
pprTickType PostInlineUnconditionally{} = text "PostInlineUnconditinaly"
pprTickType UnfoldingDone{} = text "UnfoldingDone"
pprTickType RuleFired{} = text "RuleFired"
pprTickType LetFloatFromLet = text "LetFloatFromLet"
pprTickType EtaExpansion{} = text "EtaExpansion"
pprTickType EtaReduction{} = text "EtaReduction"
pprTickType BetaReduction{} = text "BetaReduction"
pprTickType CaseOfCase{} = text "CaseOfCase"
pprTickType KnownBranch{} = text "KnownBranch"
pprTickType CaseElim{} = text "CaseElim"
pprTickType SimplifierDone = text "SimplifierDone"

pprTickCts :: Tick -> SDoc
pprTickCts (PreInlineUnconditionally v) = ppr v
pprTickCts (PostInlineUnconditionally v) = ppr v
pprTickCts (UnfoldingDone v) = ppr v
pprTickCts (RuleFired v) = ppr v
pprTickCts LetFloatFromLet = Outputable.empty
pprTickCts (EtaExpansion v) = ppr v
pprTickCts (EtaReduction v) = ppr v
pprTickCts (BetaReduction v _) = ppr v
pprTickCts (CaseOfCase v) = ppr v
pprTickCts (KnownBranch v) = ppr v
pprTickCts (CaseElim v) = ppr v
pprTickCts SimplifierDone = Outputable.empty

cmpTick :: Tick -> Tick -> Ordering
cmpTick a b = case tickToTag a `compare` tickToTag b of
  GT -> GT
  EQ -> cmpEqTick a b
  LT -> LT

cmpEqTick :: Tick -> Tick -> Ordering
cmpEqTick (PreInlineUnconditionally a) (PreInlineUnconditionally b) = a `compare` b
cmpEqTick (PostInlineUnconditionally a) (PostInlineUnconditionally b) = a `compare` b
cmpEqTick (UnfoldingDone a) (UnfoldingDone b) = a `compare` b
cmpEqTick (RuleFired a) (RuleFired b) = a `uniqCompareFS` b
cmpEqTick (EtaExpansion a) (EtaExpansion b) = a `compare` b
cmpEqTick (EtaReduction a) (EtaReduction b) = a `compare` b
cmpEqTick (BetaReduction a _) (BetaReduction b _) = a `compare` b
cmpEqTick (CaseOfCase a) (CaseOfCase b) = a `compare` b
cmpEqTick (KnownBranch a) (KnownBranch b) = a `compare` b
cmpEqTick (CaseElim a) (CaseElim b) = a `compare` b
cmpEqTick _ _ = EQ

