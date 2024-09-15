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
