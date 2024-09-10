{-# LANGUAGE DeriveTraversable #-}

module CSlash.Unit.Env where

import CSlash.Unit.External
import CSlash.Unit.State
import CSlash.Unit.Home
import CSlash.Unit.Types
import CSlash.Unit.Home.ModInfo

import CSlash.Platform
import CSlash.Settings
import CSlash.Data.Maybe
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import CSlash.Utils.Misc (HasDebugCallStack)
import CSlash.Driver.DynFlags
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module
import qualified Data.Set as Set

data UnitEnv = UnitEnv
  { ue_eps :: {-# UNPACK #-} !ExternalUnitCache
  , ue_current_unit :: UnitId
  , ue_home_unit_graph :: !HomeUnitGraph
  , ue_platform :: !Platform
  , ue_namever :: !CsNameVersion
  }

data HomeUnitEnv = HomeUnitEnv
  { homeUnitEnv_units :: !UnitState
  , homeUnitEnv_unit_dbs :: !(Maybe [UnitDatabase UnitId])
  , homeUnitEnv_dflags :: DynFlags
  , homeUnitEnv_hpt :: HomePackageTable
  , homeUnitEnv_home_unit :: !(Maybe HomeUnit)
  }

instance Outputable HomeUnitEnv where
  ppr hug = pprHPT (homeUnitEnv_hpt hug)

type HomeUnitGraph = UnitEnvGraph HomeUnitEnv

type UnitEnvGraphKey = UnitId

newtype UnitEnvGraph v = UnitEnvGraph
  { unitEnv_graph :: Map UnitEnvGraphKey v }
  deriving (Functor, Foldable, Traversable)
  
