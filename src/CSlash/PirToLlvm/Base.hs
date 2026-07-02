{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE DeriveFunctor #-}

module CSlash.PirToLlvm.Base where

import CSlash.Utils.Panic

import CSlash.Llvm
-- import GHC.CmmToLlvm.Regs
import CSlash.PirToLlvm.Config
import CSlash.PirToLlvm.Version

import CSlash.Pir.PLabel
-- import GHC.Platform.Regs ( activeStgRegs, globalRegMaybe )
import CSlash.Driver.DynFlags
import CSlash.Data.FastString
import CSlash.Pir hiding ( succ )
-- import GHC.Cmm.Utils (globalRegsOverlap)
import CSlash.Utils.Outputable as Outp
import CSlash.Platform
import CSlash.Types.Unique.FM
import CSlash.Types.Unique
import CSlash.Utils.BufHandle ( BufHandle )
import CSlash.Types.Unique.Set
import qualified CSlash.Types.Unique.DSM as DSM
import CSlash.Utils.Logger

import Control.Monad.Trans.State (StateT (..))
import Control.Applicative (Alternative((<|>)))
import Data.Maybe (fromJust, mapMaybe)

import Data.List (find, isPrefixOf)
import qualified Data.List.NonEmpty as NE
import Data.Ord (comparing)
import qualified Control.Monad.IO.Class as IO

-- ----------------------------------------------------------------------------
-- Some Data Types

-- ----------------------------------------------------------------------------
-- Environment Handling

data LlvmEnv = LlvmEnv
  { envVersion :: LlvmVersion
  , envConfig :: !LlvmCgConfig
  , envLogger :: !Logger
  , envOutput :: BufHandle
  , envTag :: !Char
  , envFreshMeta :: MetaId
  , envUniqMeta :: UniqFM Unique MetaId
  , envFunMap :: LlvmEnvMap
  , envUsedVars :: [LlvmVar]
  , envVarMap :: LlvmEnvMap
  }

type LlvmEnvMap = UniqFM Unique LlvmType

newtype LlvmM a = LlvmM { runLlvmM :: LlvmEnv -> DSM.UniqDSMT IO (a, LlvmEnv) }
  deriving stock Functor
  deriving (Applicative, Monad) via StateT LlvmEnv (DSM.UniqDSMT IO)

instance HasLogger LlvmM where
  getLogger = LlvmM $ \env -> return (envLogger env, env)

getPlatform :: LlvmM Platform
getPlatform = llvmCgPlatform <$> getConfig

getConfig :: LlvmM LlvmCgConfig
getConfig = LlvmM $ \env -> return (envConfig env, env)

instance DSM.MonadGetUnique LlvmM where
  getUniqueM = do
    tag <- getEnv envTag
    liftUDSMT $! do
      uq <- DSM.getUniqueM
      return (newTagUnique uq tag)

liftIO :: IO a -> LlvmM a
liftIO m = LlvmM $ \env -> do
  x <- IO.liftIO m
  return (x, env)

liftUDSMT :: DSM.UniqDSMT IO a -> LlvmM a
liftUDSMT m = LlvmM $ \env -> do
  x <- m
  return (x, env)

runLlvm
  :: Logger
  -> LlvmCgConfig
  -> LlvmVersion
  -> BufHandle
  -> DSM.DUniqSupply
  -> LlvmM a
  -> IO (a, DSM.DUniqSupply)
runLlvm logger cfg ver out us m = do
  ((a, _), us') <- DSM.runUDSMT us $ runLlvmM m env
  return (a, us')
  where
    env = LlvmEnv
      { envFunMap = emptyUFM
      , envVarMap = emptyUFM
      , envUsedVars = []
      , envVersion = ver
      , envConfig = cfg
      , envLogger = logger
      , envOutput = out
      , envTag = 'n'
      , envFreshMeta = MetaId 0
      , envUniqMeta = emptyUFM
      }

getEnv :: (LlvmEnv -> a) -> LlvmM a
getEnv f = LlvmM $ \env -> return (f env, env)
