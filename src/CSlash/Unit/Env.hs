{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveTraversable #-}

module CSlash.Unit.Env where

import Prelude hiding ((<>))

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

initUnitEnv :: UnitId -> HomeUnitGraph -> CsNameVersion -> Platform -> IO UnitEnv
initUnitEnv cur_unit hug namever platform = do
  eps <- initExternalUnitCache
  return $ UnitEnv
    { ue_eps = eps
    , ue_home_unit_graph = hug
    , ue_current_unit = cur_unit
    , ue_platform = platform
    , ue_namever = namever
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

mkHomeUnitEnv :: DynFlags -> HomePackageTable -> Maybe HomeUnit -> HomeUnitEnv
mkHomeUnitEnv dflags hpt home_unit = HomeUnitEnv
  { homeUnitEnv_units = emptyUnitState
  , homeUnitEnv_unit_dbs = Nothing
  , homeUnitEnv_dflags = dflags
  , homeUnitEnv_hpt = hpt
  , homeUnitEnv_home_unit = home_unit
  }

type HomeUnitGraph = UnitEnvGraph HomeUnitEnv

instance Outputable (UnitEnvGraph HomeUnitEnv) where
  ppr g = ppr [(k, length (homeUnitEnv_hpt hue)) | (k, hue) <- (unitEnv_elts g)]

type UnitEnvGraphKey = UnitId

newtype UnitEnvGraph v = UnitEnvGraph
  { unitEnv_graph :: Map UnitEnvGraphKey v }
  deriving (Functor, Foldable, Traversable)
  
unitEnv_singleton :: UnitEnvGraphKey -> v -> UnitEnvGraph v
unitEnv_singleton active m = UnitEnvGraph
  { unitEnv_graph = Map.singleton active m }

unitEnv_lookup_maybe :: UnitEnvGraphKey -> UnitEnvGraph v -> Maybe v
unitEnv_lookup_maybe u env = Map.lookup u (unitEnv_graph env)

unitEnv_lookup :: UnitEnvGraphKey -> UnitEnvGraph v -> v
unitEnv_lookup u env = fromJust $ unitEnv_lookup_maybe u env

unitEnv_elts :: UnitEnvGraph v -> [(UnitEnvGraphKey, v)]
unitEnv_elts env = Map.toList (unitEnv_graph env)

-- -------------------------------------------------------
-- Query and modify UnitState in HomeUnitEnv
-- -------------------------------------------------------

ue_units :: HasDebugCallStack => UnitEnv -> UnitState
ue_units = homeUnitEnv_units . ue_currentHomeUnitEnv

-- -------------------------------------------------------
-- Query and modify home units in HomeUnitEnv
-- -------------------------------------------------------

ue_homeUnit :: UnitEnv -> Maybe HomeUnit
ue_homeUnit = homeUnitEnv_home_unit . ue_currentHomeUnitEnv

-- -------------------------------------------------------
-- Query and modify the currently active unit
-- -------------------------------------------------------

ue_currentHomeUnitEnv :: HasDebugCallStack => UnitEnv -> HomeUnitEnv
ue_currentHomeUnitEnv e =
  case ue_findHomeUnitEnv_maybe (ue_currentUnit e) e of
    Just unitEnv -> unitEnv
    Nothing -> pprPanic "packageNotFound" $
               (ppr $ ue_currentUnit e) $$ ppr (ue_home_unit_graph e)

ue_currentUnit :: UnitEnv -> UnitId
ue_currentUnit = ue_current_unit

-- -------------------------------------------------------
-- Operations on arbitrary elements of the home unit graph
-- -------------------------------------------------------

ue_findHomeUnitEnv_maybe :: UnitId -> UnitEnv -> Maybe HomeUnitEnv
ue_findHomeUnitEnv_maybe uid e =
  unitEnv_lookup_maybe uid (ue_home_unit_graph e)

ue_findHomeUnitEnv :: HasDebugCallStack => UnitId -> UnitEnv -> HomeUnitEnv
ue_findHomeUnitEnv uid e = case unitEnv_lookup_maybe uid (ue_home_unit_graph e) of
  Nothing -> pprPanic "Unit unknown to the internal unit environment"
             $ text "unit (" <> ppr uid <> text ")"
             $$ pprUnitEnvGraph e
  Just hue -> hue

-- -----------------------------------------------------------------------------
-- Pretty output functions
-- -----------------------------------------------------------------------------

pprUnitEnvGraph :: UnitEnv -> SDoc
pprUnitEnvGraph env = text "pprInternalUnitMap"
  $$ nest 2 (pprHomeUnitGraph $ ue_home_unit_graph env)

pprHomeUnitGraph :: HomeUnitGraph -> SDoc
pprHomeUnitGraph unitEnv
  = vcat (map (\(k, v) -> pprHomeUnitEnv k v) $ Map.assocs $ unitEnv_graph unitEnv)

pprHomeUnitEnv :: UnitId -> HomeUnitEnv -> SDoc
pprHomeUnitEnv uid env =
  ppr uid <+> text "(flags:" <+> ppr (homeUnitId_ $ homeUnitEnv_dflags env)
  <> text "," <+> ppr (fmap homeUnitId $ homeUnitEnv_home_unit env)
  <> text ")" <+> text "->" $$ nest 4 (pprHPT $ homeUnitEnv_hpt env)
  
