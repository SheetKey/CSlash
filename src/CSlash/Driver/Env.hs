{-# LANGUAGE BangPatterns #-}

module CSlash.Driver.Env
  ( Cs (..)
  , CsEnv (..)
  , module CSlash.Driver.Env
  ) where

import CSlash.Driver.DynFlags
import CSlash.Driver.Errors ( printOrThrowDiagnostics )
import CSlash.Driver.Errors.Types ( CsMessage )
import CSlash.Driver.Config.Logger (initLogFlags)
import CSlash.Driver.Config.Diagnostic (initDiagOpts, initPrintConfig)
import CSlash.Driver.Env.Types ( Cs(..), CsEnv(..) )

-- import GHC.Runtime.Context
-- import GHC.Runtime.Interpreter.Types (Interp)

import CSlash.Unit
import CSlash.Unit.Module.ModGuts
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.ModDetails
import CSlash.Unit.Home.ModInfo
import CSlash.Unit.Env
import CSlash.Unit.External

-- import GHC.Core         ( CoreRule )
-- import GHC.Core.FamInstEnv
-- import GHC.Core.InstEnv

-- import GHC.Types.Annotations ( Annotation, AnnEnv, mkAnnEnv, plusAnnEnv )
import CSlash.Types.CompleteMatch
import CSlash.Types.Error ( emptyMessages, Messages )
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.TyThing

import CSlash.Builtin.Names ( cSLASH_PRIM )

import CSlash.Data.Maybe

import CSlash.Utils.Exception as Ex
import CSlash.Utils.Outputable
import CSlash.Utils.Monad
import CSlash.Utils.Panic
import CSlash.Utils.Misc
import CSlash.Utils.Logger

import Data.IORef
import qualified Data.Set as Set
import CSlash.Unit.Module.Graph

runCs :: CsEnv -> Cs a -> IO a
runCs cs_env (Cs cs) = do
  (a, w) <- cs cs_env emptyMessages
  let dflags = cs_dflags cs_env
      !diag_opts = initDiagOpts dflags
      !print_config = initPrintConfig dflags
  printOrThrowDiagnostics (cs_logger cs_env) print_config diag_opts w
  return a

runCs' :: CsEnv -> Cs a -> IO (a, Messages CsMessage)
runCs' cs_env (Cs cs) = cs cs_env emptyMessages

cs_home_unit :: CsEnv -> HomeUnit
cs_home_unit = unsafeGetHomeUnit . cs_unit_env

cs_home_unit_maybe :: CsEnv -> Maybe HomeUnit
cs_home_unit_maybe = ue_homeUnit . cs_unit_env

cs_units :: HasDebugCallStack => CsEnv -> UnitState
cs_units = ue_units . cs_unit_env

cs_HPT :: CsEnv -> HomePackageTable
cs_HPT = ue_hpt . cs_unit_env

cs_HUG :: CsEnv -> HomeUnitGraph
cs_HUG = ue_home_unit_graph . cs_unit_env

csUpdateHPT_lazy :: (HomePackageTable -> HomePackageTable) -> CsEnv -> CsEnv
csUpdateHPT_lazy f cs_env =
  let !res = updateHpt_lazy f (cs_unit_env cs_env)
  in cs_env { cs_unit_env = res }

csUpdateHUG :: (HomeUnitGraph -> HomeUnitGraph) -> CsEnv -> CsEnv
csUpdateHUG f cs_env = cs_env { cs_unit_env = updateHug f (cs_unit_env cs_env) }

cs_all_home_unit_ids :: CsEnv -> Set.Set UnitId
cs_all_home_unit_ids = unitEnv_keys . cs_HUG

csUpdateLoggerFlags :: CsEnv -> CsEnv
csUpdateLoggerFlags h = h
  { cs_logger = setLogFlags (cs_logger h) (initLogFlags (cs_dflags h)) }

mainModIs :: HomeUnitEnv -> Module
mainModIs hue = mkHomeModule (expectJust "mainModIs" $ homeUnitEnv_home_unit hue)
                             (mainModuleNameIs (homeUnitEnv_dflags hue))

csUpdateFlags :: (DynFlags -> DynFlags) -> CsEnv -> CsEnv
csUpdateFlags f h = csSetFlags (f (cs_dflags h)) h

csSetFlags :: HasDebugCallStack => DynFlags -> CsEnv -> CsEnv
csSetFlags dflags h = csUpdateLoggerFlags $ h
  { cs_dflags = dflags, cs_unit_env = ue_setFlags dflags (cs_unit_env h) }

csSetActiveHomeUnit :: HasDebugCallStack => HomeUnit -> CsEnv -> CsEnv
csSetActiveHomeUnit home_unit = csSetActiveUnitId (homeUnitId home_unit)

csSetActiveUnitId :: HasDebugCallStack => UnitId -> CsEnv -> CsEnv
csSetActiveUnitId uid e = e
  { cs_unit_env = ue_setActiveUnit uid (cs_unit_env e)
  , cs_dflags = ue_unitFlags uid (cs_unit_env e) }
