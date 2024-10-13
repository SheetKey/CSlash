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
import CSlash.Linker.Static.Utils

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

moduleGraphNodeUnitId :: ModuleGraphNode -> UnitId
moduleGraphNodeUnitId mgn =
  case mgn of
    InstantiationNode uid _iud -> uid
    ModuleNode _ ms -> toUnitId (moduleUnit (ms_mod ms))
    LinkNode _ uid -> uid

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

nodeKeyModName :: NodeKey -> Maybe ModuleName
nodeKeyModName (NodeKey_Module mk) = Just (mnkModuleName mk)
nodeKeyModName _ = Nothing

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

mgModSummaries :: ModuleGraph -> [ModSummary]
mgModSummaries mg = [ m | ModuleNode _ m <- mgModSummaries' mg ]

mgModSummaries' :: ModuleGraph -> [ModuleGraphNode]
mgModSummaries' = mg_mss

mgLookupModule :: ModuleGraph -> Module -> Maybe ModSummary
mgLookupModule ModuleGraph{..} m = listToMaybe $ mapMaybe go mg_mss
  where
    go (ModuleNode _ ms)
      | ms_mod ms == m
      = Just ms
    go _ = Nothing

emptyMG :: ModuleGraph
emptyMG = ModuleGraph [] Map.empty

extendMG :: ModuleGraph -> [NodeKey] -> ModSummary -> ModuleGraph
extendMG ModuleGraph{..} deps ms = ModuleGraph
  { mg_mss = ModuleNode deps ms : mg_mss
  , mg_trans_deps = mkTransDeps (ModuleNode deps ms : mg_mss)
  }

mkTransDeps :: [ModuleGraphNode] -> Map.Map NodeKey (Set.Set NodeKey)
mkTransDeps mss =
  let (gg, _) = moduleGraphNodes mss
  in allReachable gg (mkNodeKey . node_payload)

extendMGInst :: ModuleGraph -> UnitId -> InstantiatedUnit -> ModuleGraph
extendMGInst mg uid depUnitId = mg { mg_mss = InstantiationNode uid depUnitId : mg_mss mg }

extendMGLink :: ModuleGraph -> UnitId -> [NodeKey] -> ModuleGraph
extendMGLink mg uid nks = mg { mg_mss = LinkNode nks uid : mg_mss mg }

extendMG' :: ModuleGraph -> ModuleGraphNode -> ModuleGraph
extendMG' mg (InstantiationNode uid depUnitId) = extendMGInst mg uid depUnitId
extendMG' mg (ModuleNode deps ms) = extendMG mg deps ms
extendMG' mg (LinkNode deps uid) = extendMGLink mg uid deps

mkModuleGraph :: [ModuleGraphNode] -> ModuleGraph
mkModuleGraph = foldr (flip extendMG') emptyMG

filterToposortToModules :: [SCC ModuleGraphNode] -> [SCC ModSummary]
filterToposortToModules = mapMaybe $ mapMaybeSCC $ \case
  InstantiationNode _ _ -> Nothing
  LinkNode {} -> Nothing
  ModuleNode _ node -> Just node
  where
    mapMaybeSCC :: (a -> Maybe b) -> SCC a -> Maybe (SCC b)
    mapMaybeSCC f = \case
      AcyclicSCC a -> AcyclicSCC <$> f a
      CyclicSCC as -> case mapMaybe f as of
        [] -> Nothing
        [a] -> Just $ AcyclicSCC a
        as -> Just $ CyclicSCC as

showModMsg :: DynFlags -> Bool -> ModuleGraphNode -> SDoc
showModMsg dflags _ (LinkNode {}) =
  let staticLink = case csLink dflags of
                     LinkStaticLib -> True
                     _ -> False
      platform = targetPlatform dflags
      arch_os = platformArchOS platform
      prog_file = progFileName arch_os staticLink (outputFile_ dflags)
  in text prog_file
showModMsg _ _ (InstantiationNode _ indef_unit) =
  ppr $ instUnitInstanceOf indef_unit
showModMsg dflags recomp (ModuleNode _ mod_summary) =
  if gopt Opt_HideSourcePaths dflags
  then text mod_str
  else hsep $ [ text (mod_str ++ replicate (max 0 (16 - length mod_str)) ' ')
              , char '('
              , text (op $ msCsFilePath mod_summary) <> char ','
              , message
              , char ')' ]
  where
    op = normalise
    mod_str = moduleNameString (moduleName (ms_mod mod_summary))
              ++ csSourceString (ms_cs_src mod_summary)
    dyn_file = op $ msDynObjFilePath mod_summary
    obj_file = op $ msObjFilePath mod_summary
    files = [ obj_file ]
            ++ [ dyn_file | gopt Opt_BuildDynamicToo dflags ]
    message = case backendSpecialModuleSource (backend dflags) of
                Just special -> text special
                Nothing -> foldr1 (\ofile rest -> ofile <> comma <+> rest) (map text files)

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
