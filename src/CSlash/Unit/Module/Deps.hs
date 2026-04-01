module CSlash.Unit.Module.Deps where

import CSlash.Data.FastString

-- import GHC.Types.SafeHaskell
import CSlash.Types.Name

import CSlash.Unit.Module.Imported
import CSlash.Unit.Module
import CSlash.Unit.Home
import CSlash.Unit.State

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

mkDependencies :: HomeUnit -> Module -> ImportAvails -> Dependencies
mkDependencies home_unit mod imports =
  let all_direct_mods = imp_direct_dep_mods imports

      modDepsElts = Set.fromList . installedModuleEnvElts

      direct_mods = first moduleUnit `Set.map`
                    modDepsElts (delInstalledModuleEnv all_direct_mods (toUnitId <$> mod))

      direct_pkgs = imp_dep_direct_pkgs imports

  in Deps { dep_direct_mods = direct_mods
          , dep_direct_pkgs = direct_pkgs
          }

instance Binary Dependencies where
  put_ bh deps = do
    put_ bh (dep_direct_mods deps)
    put_ bh (dep_direct_pkgs deps)

  get bh = do dms <- get bh
              dps <- get bh
              return $ Deps dms dps

noDependencies :: Dependencies
noDependencies = Deps
  { dep_direct_mods = Set.empty
  , dep_direct_pkgs = Set.empty
  }

pprDeps :: UnitState -> Dependencies -> SDoc
pprDeps = undefined

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
  | UsageMergedRequirement
    { usg_mod :: Module
    , usg_mod_hash :: Fingerprint
    }
  deriving (Eq)

instance Binary Usage where
  put_ bh usg@UsagePackageModule{} = do
    putByte bh 0
    put_ bh (usg_mod usg)
    put_ bh (usg_mod_hash usg)
  put_ bh usg@UsageHomeModule{} = do
    putByte bh 1
    put_ bh (usg_mod_name usg)
    put_ bh (usg_unit_id usg)
    put_ bh (usg_mod_hash usg)
    put_ bh (usg_exports usg)
    put_ bh (usg_entities usg)
  put_ bh usg@UsageMergedRequirement{} = do
    putByte bh 2
    put_ bh (usg_mod usg)
    put_ bh (usg_mod_hash usg)

  get bh = do
    h <- getByte bh
    case h of
      0 -> do nm <- get bh
              mod <- get bh
              return UsagePackageModule { usg_mod = nm, usg_mod_hash = mod }
      1 -> do nm <- get bh
              uid <- get bh
              mod <- get bh
              exps <- get bh
              ents <- get bh
              return UsageHomeModule { usg_mod_name = nm, usg_mod_hash = mod, usg_unit_id = uid
                                     , usg_exports = exps, usg_entities = ents }
      2 -> do
        mod <- get bh
        hash <- get bh
        return UsageMergedRequirement { usg_mod = mod, usg_mod_hash = hash }
      i -> error ("Binary.get(Usage): " ++ show i)

data ImportAvails = ImportAvails
  { imp_mods :: ImportedMods
  , imp_direct_dep_mods :: InstalledModuleEnv ModuleName
  , imp_dep_direct_pkgs :: Set UnitId
  }
