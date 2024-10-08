module CSlash.Iface.Recomp where

import CSlash.Data.FastString

import CSlash.Driver.Backend
import CSlash.Driver.Config.Finder
import CSlash.Driver.Env
import CSlash.Driver.DynFlags
-- import GHC.Driver.Ppr
-- import GHC.Driver.Plugins

import CSlash.Iface.Syntax
import CSlash.Iface.Recomp.Binary
import CSlash.Iface.Load
-- import GHC.Iface.Recomp.Flags
-- import GHC.Iface.Env

import CSlash.Core
-- import GHC.Tc.Utils.Monad
import CSlash.Cs

import CSlash.Data.Graph.Directed
import CSlash.Data.Maybe

import CSlash.Utils.Error
import CSlash.Utils.Panic
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Misc as Utils
import CSlash.Utils.Binary
import CSlash.Utils.Fingerprint
import CSlash.Utils.Exception
import CSlash.Utils.Logger
import CSlash.Utils.Constants (debugIsOn)

-- import GHC.Types.Annotations
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.SrcLoc
import CSlash.Types.Unique.Set
import CSlash.Types.Fixity.Env
import CSlash.Types.Unique.Map
import CSlash.Unit.External
import CSlash.Unit.Finder
import CSlash.Unit.State
import CSlash.Unit.Home
import CSlash.Unit.Module
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.ModSummary
import CSlash.Unit.Module.Warnings
import CSlash.Unit.Module.Deps

import Control.Monad
import Data.List (sortBy, sort, sortOn)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Word (Word64)
import Data.Either

--Qualified import so we can define a Semigroup instance
-- but it doesn't clash with Outputable.<>
import qualified Data.Semigroup
-- import GHC.List (uncons)
import Data.Ord
import Data.Containers.ListUtils
import Data.Bifunctor
import GHC.Iface.Errors.Ppr

data RecompileRequired
  = UpToDate
  | NeedRecompile !CompileReason
  deriving Eq

data CompileReason
  = MustCompile
  | RecompBecause !RecompReason
  deriving Eq

data RecompReason
  = UnitDepRemoved UnitId
  | ModulePackageChanged FastString
  | SourceFileChanged
  | ThisUnitIdChanged
  | HieMissing
  | HieOutdated
  | ModuleChanged ModuleName
  | ModuleRemoved (UnitId, ModuleName)
  | ModuleAdded (UnitId, ModuleName)
  | ModuleChangedRaw ModuleName
  | ModuleChangedIface ModuleName
  | FileChanged FilePath
  | CustomReason String
  | FlagsChanged
  | OptimFlagsChange
  | PcFlagsChanged
  | MissingObjectFile
  | MissingDynObjectFile
  | MissingDynHiFile
  | MismatchedDynHiFile
  | ObjectsChange
  | LibraryChanged
  deriving Eq
