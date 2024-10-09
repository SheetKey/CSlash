{-# LANGUAGE BangPatterns #-}
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

unsafeGetHomeUnit :: UnitEnv -> HomeUnit
unsafeGetHomeUnit ue = ue_unsafeHomeUnit ue

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

unitEnv_insert :: UnitEnvGraphKey -> v -> UnitEnvGraph v -> UnitEnvGraph v
unitEnv_insert unitId env unitEnv = unitEnv
  { unitEnv_graph = Map.insert unitId env (unitEnv_graph unitEnv) }

unitEnv_delete :: UnitEnvGraphKey -> UnitEnvGraph v -> UnitEnvGraph v
unitEnv_delete uid unitEnv = unitEnv
  { unitEnv_graph = Map.delete uid (unitEnv_graph unitEnv) }
  
unitEnv_singleton :: UnitEnvGraphKey -> v -> UnitEnvGraph v
unitEnv_singleton active m = UnitEnvGraph
  { unitEnv_graph = Map.singleton active m }

unitEnv_adjust :: (v -> v) -> UnitEnvGraphKey -> UnitEnvGraph v -> UnitEnvGraph v
unitEnv_adjust f uid unitEnv = unitEnv
  { unitEnv_graph = Map.adjust f uid (unitEnv_graph unitEnv) }

unitEnv_member :: UnitEnvGraphKey -> UnitEnvGraph v -> Bool
unitEnv_member u env = Map.member u (unitEnv_graph env)

unitEnv_lookup_maybe :: UnitEnvGraphKey -> UnitEnvGraph v -> Maybe v
unitEnv_lookup_maybe u env = Map.lookup u (unitEnv_graph env)

unitEnv_lookup :: UnitEnvGraphKey -> UnitEnvGraph v -> v
unitEnv_lookup u env = fromJust $ unitEnv_lookup_maybe u env

unitEnv_keys :: UnitEnvGraph v -> Set.Set UnitEnvGraphKey
unitEnv_keys env = Map.keysSet (unitEnv_graph env)

unitEnv_elts :: UnitEnvGraph v -> [(UnitEnvGraphKey, v)]
unitEnv_elts env = Map.toList (unitEnv_graph env)

-- -------------------------------------------------------
-- Query and modify UnitState in HomeUnitEnv
-- -------------------------------------------------------

ue_units :: HasDebugCallStack => UnitEnv -> UnitState
ue_units = homeUnitEnv_units . ue_currentHomeUnitEnv

-- -------------------------------------------------------
-- Query and modify DynFlags in HomeUnitEnv
-- -------------------------------------------------------

ue_setFlags :: HasDebugCallStack => DynFlags -> UnitEnv -> UnitEnv
ue_setFlags dflags ue_env = ue_setUnitFlags (ue_currentUnit ue_env) dflags ue_env

ue_setUnitFlags :: HasDebugCallStack => UnitId -> DynFlags -> UnitEnv -> UnitEnv
ue_setUnitFlags uid dflags e = ue_updateUnitFlags (const dflags) uid e

ue_unitFlags :: HasDebugCallStack => UnitId -> UnitEnv -> DynFlags
ue_unitFlags uid ue_env = homeUnitEnv_dflags $ ue_findHomeUnitEnv uid ue_env

ue_updateUnitFlags :: HasDebugCallStack => (DynFlags -> DynFlags) -> UnitId -> UnitEnv -> UnitEnv
ue_updateUnitFlags f uid e = ue_updateHomeUnitEnv update uid e
  where
    update hue = hue { homeUnitEnv_dflags = f $ homeUnitEnv_dflags hue }

-- -------------------------------------------------------
-- Query and modify home units in HomeUnitEnv
-- -------------------------------------------------------

ue_homeUnit :: UnitEnv -> Maybe HomeUnit
ue_homeUnit = homeUnitEnv_home_unit . ue_currentHomeUnitEnv

ue_unsafeHomeUnit :: UnitEnv -> HomeUnit
ue_unsafeHomeUnit ue = case ue_homeUnit ue of
  Nothing -> panic "unsafeGetHomeUnit: No home unit"
  Just h -> h

-- -------------------------------------------------------
-- Query and modify the currently active unit
-- -------------------------------------------------------

ue_currentHomeUnitEnv :: HasDebugCallStack => UnitEnv -> HomeUnitEnv
ue_currentHomeUnitEnv e =
  case ue_findHomeUnitEnv_maybe (ue_currentUnit e) e of
    Just unitEnv -> unitEnv
    Nothing -> pprPanic "packageNotFound" $
               (ppr $ ue_currentUnit e) $$ ppr (ue_home_unit_graph e)

ue_setActiveUnit :: UnitId -> UnitEnv -> UnitEnv
ue_setActiveUnit u ue_env = assertUnitEnvInvariant $ ue_env
  { ue_current_unit = u }

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

ue_updateHomeUnitEnv :: (HomeUnitEnv -> HomeUnitEnv) -> UnitId -> UnitEnv -> UnitEnv
ue_updateHomeUnitEnv f uid e = e
  { ue_home_unit_graph = unitEnv_adjust f uid $ ue_home_unit_graph e }

ue_renameUnitId :: HasDebugCallStack => UnitId -> UnitId -> UnitEnv -> UnitEnv
ue_renameUnitId oldUnit newUnit unitEnv = case ue_findHomeUnitEnv_maybe oldUnit unitEnv of
  Nothing ->
    pprPanic "Tried to rename unit, but it didn't exist"
    $ text "Rename old unit \"" <> ppr oldUnit <> text "\" to \"" <> ppr newUnit <> text "\""
    $$ nest 2 (pprUnitEnvGraph unitEnv)
  Just oldEnv ->
    let activeUnit :: UnitId
        !activeUnit = if ue_currentUnit unitEnv == oldUnit
                      then newUnit
                      else ue_currentUnit unitEnv
        newInternalUnitEnv = oldEnv
          { homeUnitEnv_dflags = (homeUnitEnv_dflags oldEnv)
                                 { homeUnitId_ = newUnit }
          }
    in unitEnv
       { ue_current_unit = activeUnit
       , ue_home_unit_graph =
           unitEnv_insert newUnit newInternalUnitEnv
           $ unitEnv_delete oldUnit
           $ ue_home_unit_graph unitEnv
       }

-- ---------------------------------------------
-- Asserts to enforce invariants for the UnitEnv
-- ---------------------------------------------

assertUnitEnvInvariant :: HasDebugCallStack => UnitEnv -> UnitEnv
assertUnitEnvInvariant u =
  if ue_current_unit u `unitEnv_member` ue_home_unit_graph u
  then u
  else pprPanic "invariant" (ppr (ue_current_unit u) $$ ppr (ue_home_unit_graph u))

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
  
