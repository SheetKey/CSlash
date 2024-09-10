{-# LANGUAGE DerivingVia #-}

module CSlash.Driver.Env.Types where

import CSlash.Driver.Errors.Types ( CsMessage )
-- import {-# SOURCE #-} GHC.Driver.Hooks
import CSlash.Driver.DynFlags ( ContainsDynFlags(..), HasDynFlags(..), DynFlags )
import CSlash.Driver.LlvmConfigCache (LlvmConfigCache)

-- import GHC.Runtime.Context
-- import GHC.Runtime.Interpreter.Types ( Interp )
import CSlash.Types.Error ( Messages )
import CSlash.Types.Name.Cache
import CSlash.Types.Target
import CSlash.Types.TypeEnv
import CSlash.Unit.Finder.Types
import CSlash.Unit.Module.Graph
import CSlash.Unit.Env
import CSlash.Utils.Logger
import CSlash.Utils.TmpFs
-- import {-# SOURCE #-} GHC.Driver.Plugins

import Control.Monad.IO.Class
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State
import Data.IORef
import CSlash.Driver.Env.KnotVars

newtype Cs a = Cs (CsEnv -> Messages CsMessage -> IO (a, Messages CsMessage))
  deriving (Functor, Applicative, Monad, MonadIO)
    via ReaderT CsEnv (StateT (Messages CsMessage) IO)

instance HasDynFlags Cs where
  getDynFlags = Cs $ \ e w -> return (cs_dflags e, w)

instance ContainsDynFlags CsEnv where
  extractDynFlags h = cs_dflags h

instance HasLogger Cs where
  getLogger = Cs $ \ e w -> return (cs_logger e, w)

data CsEnv = CsEnv
  { cs_dflags :: DynFlags
  , cs_targets :: [Target]
  , cs_mod_graph :: ModuleGraph
  , cs_NC :: {-# UNPACK #-} !NameCache
  , cd_FC :: {-# UNPACK #-} !FinderCache
  , cs_type_env_vars :: KnotVars (IORef TypeEnv)
  , cs_unit_env :: UnitEnv
  , cs_logger :: !Logger
  , cs_tmpfs :: !TmpFs
  , cs_llvm_config :: !LlvmConfigCache
  }
