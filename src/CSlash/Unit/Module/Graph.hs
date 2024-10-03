{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveTraversable #-}

module CSlash.Unit.Module.Graph where

import Prelude hiding ((<>))

import CSlash.Platform

import CSlash.Data.Maybe
import CSlash.Data.Graph.Directed

import CSlash.Driver.Backend
import CSlash.Driver.DynFlags

import CSlash.Types.SourceFile ( csSourceString )

import CSlash.Unit.Module.ModSummary
import CSlash.Unit.Types
import CSlash.Utils.Outputable
import CSlash.Utils.Misc ( partitionWith )

import System.FilePath
import qualified Data.Map as Map
import CSlash.Types.Unique.DSet
import qualified Data.Set as Set
import Data.Set (Set)
import CSlash.Unit.Module
-- import GHC.Linker.Static.Utils

import Data.Bifunctor
import Data.Function
import Data.List (sort)
import CSlash.Data.List.SetOps

data ModuleGraphNode
  = InstantiationNode UnitId InstantiatedUnit
  | ModuleNode [NodeKey] ModSummary
  | LinkNode [NodeKey] UnitId

moduleGraphNodeModule :: ModuleGraphNode -> Maybe ModuleName
moduleGraphNodeModule mgn = ms_mod_name <$> (moduleGraphNodeModSum mgn)

moduleGraphNodeModSum :: ModuleGraphNode -> Maybe ModSummary
moduleGraphNodeModSum (InstantiationNode {}) = Nothing
moduleGraphNodeModSum (LinkNode {}) = Nothing
moduleGraphNodeModSum (ModuleNode _ ms) = Just ms


instance Outputable ModuleGraphNode where
  ppr = \case
    InstantiationNode _ iuid -> ppr iuid
    ModuleNode nks ms -> ppr (msKey ms) <+> ppr nks
    LinkNode uid _ -> text "LN:" <+> ppr uid

instance Eq ModuleGraphNode where
  (==) = (==) `on` mkNodeKey

instance Ord ModuleGraphNode where
  compare = compare `on` mkNodeKey

data NodeKey
  = NodeKey_Unit {-# UNPACK #-} !InstantiatedUnit
  | NodeKey_Module {-# UNPACK #-} !ModNodeKeyWithUid
  | NodeKey_Link !UnitId
  deriving (Eq, Ord)

instance Outputable NodeKey where
  ppr nk = pprNodeKey nk

pprNodeKey :: NodeKey -> SDoc
pprNodeKey (NodeKey_Unit iu) = ppr iu
pprNodeKey (NodeKey_Module mk) = ppr mk
pprNodeKey (NodeKey_Link uid) = ppr uid

data ModNodeKeyWithUid = ModNodeKeyWithUid
  { mnkModuleName :: !ModuleName
  , mnkUnitId :: !UnitId
  }
  deriving (Eq, Ord)

instance Outputable ModNodeKeyWithUid where
  ppr (ModNodeKeyWithUid mnwib uid) = ppr uid <> colon <> ppr mnwib

data ModuleGraph = ModuleGraph
  { mg_mss :: [ModuleGraphNode]
  , mg_trans_deps :: Map.Map NodeKey (Set.Set NodeKey)
  }

mapMG :: (ModSummary -> ModSummary) -> ModuleGraph -> ModuleGraph
mapMG f mg@ModuleGraph{..} = mg
  { mg_mss = flip fmap mg_mss $ \case
      InstantiationNode uid iuid -> InstantiationNode uid iuid
      LinkNode uid nks -> LinkNode uid nks
      ModuleNode deps ms -> ModuleNode deps (f ms)
  }

unionMG :: ModuleGraph -> ModuleGraph -> ModuleGraph
unionMG a b =
  let new_mss = nubOrdBy compare $ mg_mss a `mappend` mg_mss b
  in ModuleGraph
     { mg_mss = new_mss
     , mg_trans_deps = mkTransDeps new_mss
     }

emptyMG :: ModuleGraph
emptyMG = ModuleGraph [] Map.empty

mkTransDeps :: [ModuleGraphNode] -> Map.Map NodeKey (Set.Set NodeKey)
mkTransDeps mss =
  let (gg, _) = moduleGraphNodes mss
  in allReachable gg (mkNodeKey . node_payload)

type SummaryNode = Node Int ModuleGraphNode

summaryNodeKey :: SummaryNode -> Int
summaryNodeKey = node_key

summaryNodeSummary :: SummaryNode -> ModuleGraphNode
summaryNodeSummary = node_payload

nodeDependencies :: ModuleGraphNode -> [NodeKey]
nodeDependencies = \case
  LinkNode deps _ -> deps
  InstantiationNode uid iuid ->
    NodeKey_Module
    . (\mod -> ModNodeKeyWithUid mod uid)
    <$> uniqDSetToList (instUnitHoles iuid)
  ModuleNode deps _ -> deps

moduleGraphNodes :: [ModuleGraphNode] -> (Graph SummaryNode, NodeKey -> Maybe SummaryNode)
moduleGraphNodes summaries =
  (graphFromEdgedVerticesUniq nodes, lookup_node)
  where
    nodes = go <$> numbered_summaries
      where
        go (s, key) = let lkup_key = ms_mod <$> moduleGraphNodeModSum s
                      in DigraphNode s key $ out_edge_keys $ nodeDependencies s

    numbered_summaries = zip summaries [1..]

    lookup_node :: NodeKey -> Maybe SummaryNode
    lookup_node key = Map.lookup key (unNodeMap node_map)

    lookup_key :: NodeKey -> Maybe Int
    lookup_key = fmap summaryNodeKey . lookup_node
 
    node_map :: NodeMap SummaryNode
    node_map = NodeMap $ Map.fromList
               [ (mkNodeKey s, node)
               | node <- nodes
               , let s = summaryNodeSummary node
               ]

    out_edge_keys :: [NodeKey] -> [Int]
    out_edge_keys = mapMaybe lookup_key

newtype NodeMap a = NodeMap { unNodeMap :: Map.Map NodeKey a }
  deriving (Functor, Traversable, Foldable)

mkNodeKey :: ModuleGraphNode -> NodeKey
mkNodeKey = \case
  InstantiationNode _ iu -> NodeKey_Unit iu
  ModuleNode _ x -> NodeKey_Module $ msKey x
  LinkNode _ uid -> NodeKey_Link uid

msKey :: ModSummary -> ModNodeKeyWithUid
msKey ms = ModNodeKeyWithUid (ms_mod_name ms) (ms_unitid ms)
