{-# LANGUAGE DeriveFunctor #-}

module CSlash.Driver.Env.KnotVars where

import CSlash.Unit.Types ( Module )
import CSlash.Unit.Module.Env
import Data.Maybe
import CSlash.Utils.Outputable

data KnotVars a
  = KnotVars
    { kv_domain :: [Module]
    , kv_lookup :: Module -> Maybe a
    }
  | NoKnotVars
  deriving Functor

instance Outputable (KnotVars a) where
  ppr NoKnotVars = text "NoKnot"
  ppr (KnotVars dom _) = text "Knotty:" <+> ppr dom

emptyKnotVars :: KnotVars a
emptyKnotVars = NoKnotVars

knotVarsFromModuleEnv :: ModuleEnv a -> KnotVars a
knotVarsFromModuleEnv me | isEmptyModuleEnv me = NoKnotVars
knotVarsFromModuleEnv me = KnotVars (moduleEnvKeys me) (lookupModuleEnv me)

lookupKnotVars :: KnotVars a -> Module -> Maybe a
lookupKnotVars (KnotVars _ lookup) x = lookup x
lookupKnotVars NoKnotVars _ = Nothing
