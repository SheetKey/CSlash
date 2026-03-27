module CSlash.CsToCore.Usage where

import CSlash.Cs.Pass

import CSlash.Driver.Env

import CSlash.Tc.Types

import CSlash.Iface.Load

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Fingerprint
import CSlash.Utils.Panic
import CSlash.Utils.Monad

import CSlash.Types.Name
import CSlash.Types.Name.Set ( NameSet, allUses )
import CSlash.Types.Unique.Set

import CSlash.Unit
import CSlash.Unit.Env
import CSlash.Unit.External
import CSlash.Unit.Module.Imported
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.Deps

import CSlash.Data.Maybe
import CSlash.Data.FastString

import Data.IORef
import Data.List (sortBy)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List.NonEmpty as NE

import CSlash.Linker.Types
import CSlash.Unit.Finder
import CSlash.Types.Unique.DFM

mkUsedNames :: TcGblEnv Zk -> NameSet
mkUsedNames TcGblEnv { tcg_dus = dus } = allUses dus
