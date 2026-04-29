{-# LANGUAGE PatternSynonyms #-}

module CSlash.Core.Opt.Simplify.Monad where

import CSlash.Cs.Pass

import CSlash.Types.Var
import CSlash.Types.Name
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.Opt.Stats
import CSlash.Core.Rules
import CSlash.Core.Utils
import CSlash.Types.Unique.Supply
import CSlash.Driver.Flags
import CSlash.Utils.Outputable
import CSlash.Data.FastString
import CSlash.Utils.Monad
import CSlash.Utils.Logger as Logger
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Types.Basic
import Control.Monad ( ap )

import GHC.Exts( oneShot )

{- *********************************************************************
*                                                                      *
        Monad plumbing
*                                                                      *
********************************************************************* -}

newtype SimplM result = SM'
  { unSM :: SimplTopEnv -> SimplCount -> IO (result, SimplCount) }

pattern SM :: (SimplTopEnv -> SimplCount -> IO (result, SimplCount)) -> SimplM result
pattern SM m <- SM' m
  where
    SM m = SM' (oneShot $ \env -> oneShot $ \ct -> m env ct)

data TopEnvConfig = TopEnvConfig
  { te_history_size :: !Int
  , te_tick_factor :: !Int
  }

data SimplTopEnv = STE
  { st_config :: !TopEnvConfig
  , st_logger :: !Logger
  , st_max_ticks :: !IntWithInf
  , st_read_ruleenv :: !(IO RuleEnv)
  }

initSimpl
  :: Logger
  -> IO RuleEnv
  -> TopEnvConfig
  -> Int
  -> SimplM a
  -> IO (a, SimplCount)
initSimpl logger read_ruleenv cfg size m = do
  let simplCount = zeroSimplCount $ logHasDumpFlag logger Opt_D_dump_simpl_stats
  unSM m env simplCount
  where
    env = STE { st_config = cfg
              , st_logger = logger
              , st_max_ticks = computeMaxTicks cfg size
              , st_read_ruleenv = read_ruleenv
              }

computeMaxTicks :: TopEnvConfig -> Int -> IntWithInf
computeMaxTicks cfg size
  = treatZeroAsInf $ fromInteger ((toInteger (size + base_size)
                                   * toInteger (tick_factor * magic_multiplier))
                                   `div` 100)
  where
    tick_factor = te_tick_factor cfg
    base_size = 100
    magic_multiplier = 40

instance Functor SimplM where
  fmap = mapSmpl

instance Applicative SimplM where
  pure = returnSmpl
  (<*>) = ap
  (*>) = thenSmpl_

instance Monad SimplM where
  (>>) = (*>)
  (>>=) = thenSmpl

{-# INLINE mapSmpl #-}
mapSmpl :: (a -> b) -> SimplM a -> SimplM b
mapSmpl f m = thenSmpl m (returnSmpl . f)

{-# INLINE returnSmpl #-}
returnSmpl :: a -> SimplM a
returnSmpl e = SM (\_ sc -> return (e, sc))

{-# INLINE thenSmpl_ #-}
thenSmpl_ :: SimplM a -> SimplM b -> SimplM b
thenSmpl_ m k = SM $ \st_env sc0 -> do
  (_, sc1) <- unSM m st_env sc0
  unSM k st_env sc1

{-# INLINE thenSmpl #-}
thenSmpl :: SimplM a -> (a -> SimplM b) -> SimplM b
thenSmpl m k = SM $ \st_env sc0 -> do
  (m_result, sc1) <- unSM m st_env sc0
  unSM (k m_result) st_env sc1

{-# INLINE traceSmpl #-}
traceSmpl :: String -> SDoc -> SimplM ()
traceSmpl herald doc = do
  logger <- getLogger
  liftIO $ Logger.putDumpFileMaybe logger Opt_D_dump_simpl_trace "Simpl Trace"
    FormatText (hang (text herald) 2 doc)

{- *********************************************************************
*                                                                      *
        The unique supply
*                                                                      *
********************************************************************* -}

simplTag :: Char
simplTag = 's'

instance MonadUnique SimplM where
  getUniqueSupplyM = liftIO $ mkSplitUniqSupply simplTag
  getUniqueM = liftIO $ uniqFromTag simplTag

instance HasLogger SimplM where
  getLogger = gets st_logger

instance MonadIO SimplM where
  liftIO = liftIOWithEnv . const

getSimplRules :: SimplM RuleEnv
getSimplRules = liftIOWithEnv st_read_ruleenv

liftIOWithEnv :: (SimplTopEnv -> IO a) -> SimplM a
liftIOWithEnv m = SM $ \st_env sc -> do
  x <- m st_env
  return (x, sc)

gets :: (SimplTopEnv -> a) -> SimplM a
gets f = liftIOWithEnv (return . f)

newId :: FastString -> (Type Zk) -> SimplM (Id Zk)
newId fs ty = mkSysLocalM fs ty

{- *********************************************************************
*                                                                      *
        Counting
*                                                                      *
********************************************************************* -}

getSimplCount :: SimplM SimplCount
getSimplCount = SM $ \_ sc -> return (sc, sc)

tick :: Tick -> SimplM ()
tick t = SM $ \st_env sc -> panic "tick"
  -- let history_size = te_history_size (st_config st_env)
  --     sc' = doSimplTick history_size t sc
  -- in sc' `seq` return ((), sc'))
