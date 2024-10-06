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
-- import GHC.Unit.Module.ModGuts
-- import GHC.Unit.Module.ModIface
-- import GHC.Unit.Module.ModDetails
-- import GHC.Unit.Home.ModInfo
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

cs_home_unit_maybe :: CsEnv -> Maybe HomeUnit
cs_home_unit_maybe = ue_homeUnit . cs_unit_env

cs_units :: HasDebugCallStack => CsEnv -> UnitState
cs_units = ue_units . cs_unit_env

cs_HUG :: CsEnv -> HomeUnitGraph
cs_HUG = ue_home_unit_graph . cs_unit_env

cs_all_home_unit_ids :: CsEnv -> Set.Set UnitId
cs_all_home_unit_ids = unitEnv_keys . cs_HUG

csUpdateLoggerFlags :: CsEnv -> CsEnv
csUpdateLoggerFlags h = h
  { cs_logger = setLogFlags (cs_logger h) (initLogFlags (cs_dflags h)) }

csSetActiveUnitId :: HasDebugCallStack => UnitId -> CsEnv -> CsEnv
csSetActiveUnitId uid e = e
  { cs_unit_env = ue_setActiveUnit uid (cs_unit_env e)
  , cs_dflags = ue_unitFlags uid (cs_unit_env e) }
