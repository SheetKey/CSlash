module CSlash.Unit.Module.Deps where

import CSlash.Data.FastString

-- import GHC.Types.SafeHaskell
import CSlash.Types.Name

import CSlash.Unit.Module.Imported
import CSlash.Unit.Module
import CSlash.Unit.Home
-- import GHC.Unit.State

import CSlash.Utils.Fingerprint
import CSlash.Utils.Binary
import CSlash.Utils.Outputable

import Data.List (sortBy, sort, partition)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Bifunctor

data Dependencies = Deps
  { dep_direct_mods :: Set (UnitId, ModuleName)
  , dep_direct_pkgs :: Set UnitId
  }

data Usage
  = UsagePackageModule -- module from another package
    { usg_mod :: Module
    , usg_mod_hash :: Fingerprint
    }
  | UsageHomeModule -- module from the current package
    { usg_mod_name :: ModuleName
    , usg_unit_id :: UnitId
    , usg_mod_hash :: Fingerprint
    , usg_entities :: [(OccName, Fingerprint)]
    , usg_exports :: Maybe Fingerprint
    }
  deriving (Eq)
