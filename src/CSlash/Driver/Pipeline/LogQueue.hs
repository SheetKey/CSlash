{-# LANGUAGE BangPatterns #-}

module CSlash.Driver.Pipeline.LogQueue where

import Control.Concurrent
import Data.IORef
import CSlash.Types.Error
import CSlash.Types.SrcLoc
import CSlash.Utils.Logger
import qualified Data.IntMap as IM
import Control.Concurrent.STM
import Control.Monad

data LogQueue = LogQueue
  { logQueueId :: !Int
  , logQueueMessages :: !(IORef [Maybe (MessageClass, SrcSpan, SDoc, LogFlags)])
  , logQueueSemaphore :: !(MVar ())
  }

newLogQueue :: Int -> IO LogQueue
newLogQueue n = do
  mqueue <- newIORef []
  sem <- newMVar ()
  return (LogQueue n mqueue sem)

finishLogQueue :: LogQueue -> IO ()
finishLogQueue lq = writeLogQueueInternal lq Nothing

writeLogQueue :: LogQueue -> (MessageClass,SrcSpan,SDoc, LogFlags) -> IO ()
writeLogQueue lq msg = writeLogQueueInternal lq (Just msg)

writeLogQueueInternal :: LogQueue -> Maybe (MessageClass,SrcSpan,SDoc, LogFlags) -> IO ()
writeLogQueueInternal (LogQueue _n ref sem) msg = do
  atomicModifyIORef' ref $ \msgs -> (msg:msgs,())
  _ <- tryPutMVar sem ()
  return ()

parLogAction :: LogQueue -> LogAction
parLogAction log_queue log_flags !msgClass !srcSpan !msg =
  writeLogQueue log_queue (msgClass,srcSpan,msg, log_flags)

printLogs :: Logger -> LogQueue -> IO ()
printLogs !logger (LogQueue _n ref sem) = read_msgs
  where
    read_msgs = do
      takeMVar sem
      msgs <- atomicModifyIORef' ref $ \xs -> ([], reverse xs)
      print_loop msgs

    print_loop [] = read_msgs
    print_loop (x:xs) = case x of
      Just (msgClass,srcSpan,msg,flags) -> do
        logMsg (setLogFlags logger flags) msgClass srcSpan msg
        print_loop xs
      Nothing -> return ()

data LogQueueQueue = LogQueueQueue Int (IM.IntMap LogQueue)

newLogQueueQueue :: LogQueueQueue
newLogQueueQueue = LogQueueQueue 1 IM.empty

addToQueueQueue :: LogQueue -> LogQueueQueue -> LogQueueQueue
addToQueueQueue lq (LogQueueQueue n im) = LogQueueQueue n (IM.insert (logQueueId lq) lq im)

initLogQueue :: TVar LogQueueQueue -> LogQueue -> STM ()
initLogQueue lqq lq = modifyTVar lqq (addToQueueQueue lq)

allLogQueues :: LogQueueQueue -> [LogQueue]
allLogQueues (LogQueueQueue _n im) = IM.elems im

dequeueLogQueueQueue :: LogQueueQueue -> Maybe (LogQueue, LogQueueQueue)
dequeueLogQueueQueue (LogQueueQueue n lqq) = case IM.minViewWithKey lqq of
  Just ((k, v), lqq') | k == n -> Just (v, LogQueueQueue (n + 1) lqq')
  _ -> Nothing

logThread :: Logger -> TVar Bool -> TVar LogQueueQueue -> IO (IO ())
logThread logger stopped lqq_var = do
  finished_var <- newEmptyMVar
  _ <- forkIO $ print_logs *> putMVar finished_var ()
  return (takeMVar finished_var)
  where
    finish = mapM (printLogs logger)

    print_logs = join $ atomically $ do
      lqq <- readTVar lqq_var
      case dequeueLogQueueQueue lqq of
        Just (lq, lqq') -> do
          writeTVar lqq_var lqq'
          return (printLogs logger lq *> print_logs)
        Nothing -> do
          stopped <- readTVar stopped
          if not stopped then retry
                         else return (finish (allLogQueues lqq))
