{-# LANGUAGE LambdaCase #-}

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
-- import GHC.Data.List.SetOps

data ModuleGraphNode
  = InstantiationNode UnitId InstantiatedUnit
  | ModuleNode [NodeKey] ModSummary
  | LinkNode [NodeKey] UnitId

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

mkNodeKey :: ModuleGraphNode -> NodeKey
mkNodeKey = \case
  InstantiationNode _ iu -> NodeKey_Unit iu
  ModuleNode _ x -> NodeKey_Module $ msKey x
  LinkNode _ uid -> NodeKey_Link uid

msKey :: ModSummary -> ModNodeKeyWithUid
msKey ms = ModNodeKeyWithUid (ms_mod_name ms) (ms_unitid ms)
