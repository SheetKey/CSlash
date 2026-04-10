module CSlash.Unit.External where

import CSlash.Unit
import CSlash.Unit.Module.ModIface

-- import GHC.Core.FamInstEnv
-- import GHC.Core.InstEnv ( InstEnv, emptyInstEnv )
import CSlash.Core.Opt.ConstantFold
import CSlash.Core.Rules ( RuleBase, mkRuleBase)

-- import GHC.Types.Annotations ( AnnEnv, emptyAnnEnv )
import CSlash.Types.CompleteMatch
import CSlash.Types.TypeEnv
import CSlash.Types.Unique.DSet

import Data.IORef

type PackageTypeEnv = TypeEnv
type PackageRuleBase = RuleBase
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
  , eps_rule_base = mkRuleBase builtinRules
  , eps_complete_matches = []
  , eps_stats = EpsStats
                { n_ifaces_in = 0
                , n_decls_in = 0
                , n_decls_out = 0
                , n_rules_in = length builtinRules
                , n_rules_out = 0
                }
  }

data ExternalPackageState = EPS
  { eps_PIT :: !PackageIfaceTable
  , eps_free_holes :: InstalledModuleEnv (UniqDSet ModuleName)
  , eps_PTE :: !PackageTypeEnv
  , eps_rule_base :: !PackageRuleBase
  , eps_complete_matches :: !PackageCompleteMatches
  , eps_stats :: !EpsStats
  }

data EpsStats = EpsStats
  { n_ifaces_in :: !Int
  , n_decls_in :: !Int
  , n_decls_out :: !Int
  , n_rules_in :: !Int
  , n_rules_out :: !Int
  }

addEpsInStats :: EpsStats -> Int -> Int -> EpsStats
addEpsInStats stats n_decls n_rules  = stats
  { n_ifaces_in = n_ifaces_in stats + 1
  , n_decls_in = n_decls_in stats + n_decls
  , n_rules_in = n_rules_in stats + n_rules
  }
