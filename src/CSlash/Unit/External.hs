module CSlash.Unit.External where

import CSlash.Unit
import CSlash.Unit.Module.ModIface

-- import GHC.Core.FamInstEnv
-- import GHC.Core.InstEnv ( InstEnv, emptyInstEnv )
-- import GHC.Core.Opt.ConstantFold
-- import GHC.Core.Rules ( RuleBase, mkRuleBase)

-- import GHC.Types.Annotations ( AnnEnv, emptyAnnEnv )
import CSlash.Types.CompleteMatch
import CSlash.Types.TypeEnv
import CSlash.Types.Unique.DSet

import Data.IORef

type PackageTypeEnv = TypeEnv
type PackageCompleteMatches = CompleteMatches

type PackageIfaceTable = ModuleEnv ModIface

emptyPackageIfaceTable :: PackageIfaceTable
emptyPackageIfaceTable = emptyModuleEnv

newtype ExternalUnitCache = ExternalUnitCache
  { euc_eps :: IORef ExternalPackageState }

initExternalUnitCache :: IO ExternalUnitCache
initExternalUnitCache = ExternalUnitCache <$> newIORef initExternalPackageState

initExternalPackageState :: ExternalPackageState
initExternalPackageState = EPS
  { eps_PIT = emptyPackageIfaceTable
  , eps_free_holes = emptyInstalledModuleEnv
  , eps_PTE = emptyTypeEnv
  , eps_complete_matches = []
  , eps_stats = EpsStats
                { n_ifaces_in = 0
                , n_decls_in = 0
                , n_decls_out = 0
                }
  }

data ExternalPackageState = EPS
  { eps_PIT :: !PackageIfaceTable
  , eps_free_holes :: InstalledModuleEnv (UniqDSet ModuleName)
  , eps_PTE :: !PackageTypeEnv
  , eps_complete_matches :: !PackageCompleteMatches
  , eps_stats :: !EpsStats
  }

data EpsStats = EpsStats
  { n_ifaces_in :: !Int
  , n_decls_in :: !Int
  , n_decls_out :: !Int
  }
