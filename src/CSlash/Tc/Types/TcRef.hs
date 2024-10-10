{-# LANGUAGE BangPatterns #-}

module CSlash.Tc.Types.TcRef where

import Control.Monad.IO.Class
import Data.IORef

type TcRef a = IORef a

newTcRef :: MonadIO m => a -> m (TcRef a)
newTcRef = \ a -> liftIO $ newIORef a
{-# INLINE newTcRef #-}

readTcRef :: MonadIO m => TcRef a -> m a
readTcRef = \ ref -> liftIO $ readIORef ref
{-# INLINE readTcRef #-}

writeTcRef :: MonadIO m => TcRef a -> a -> m ()
writeTcRef = \ ref a -> liftIO $ writeIORef ref a
{-# INLINE writeTcRef #-}

updTcRef :: MonadIO m => TcRef a -> (a -> a) -> m ()
updTcRef = \ ref fn -> liftIO $ modifyIORef' ref fn
{-# INLINE updTcRef #-}

updTcRefM :: MonadIO m => TcRef a -> (a -> m a) -> m ()
updTcRefM ref upd
  = do { contents      <- readTcRef ref
       ; !new_contents <- upd contents
       ; writeTcRef ref new_contents }
{-# INLINE updTcRefM #-}
