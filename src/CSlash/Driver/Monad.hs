{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE NoPolyKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -funbox-strict-fields #-}

module CSlash.Driver.Monad where

import CSlash.Driver.DynFlags
import CSlash.Driver.Env
import CSlash.Driver.Errors ( printOrThrowDiagnostics, printMessages )
import CSlash.Driver.Errors.Types
import CSlash.Driver.Config.Diagnostic

import CSlash.Utils.Monad
import CSlash.Utils.Exception
import CSlash.Utils.Error
import CSlash.Utils.Logger

import CSlash.Types.SrcLoc
import CSlash.Types.SourceError

import Control.Monad
import Control.Monad.Catch as MC
import Control.Monad.Trans.Reader
import Data.IORef

class (Functor m, ExceptionMonad m, HasDynFlags m, HasLogger m) => CslMonad m where
  getSession :: m CsEnv
  setSession :: CsEnv -> m ()

withSession :: CslMonad m => (CsEnv -> m a) -> m a
withSession f = getSession >>= f

getSessionDynFlags :: CslMonad m => m DynFlags
getSessionDynFlags = withSession (return . cs_dflags)

modifySession :: CslMonad m => (CsEnv -> CsEnv) -> m ()
modifySession f = do
  h <- getSession
  setSession $! f h

modifySessionM :: CslMonad m => (CsEnv -> m CsEnv) -> m ()
modifySessionM f = do
  h <- getSession
  h' <- f h
  setSession $! h'

withSavedSession :: CslMonad m => m a -> m a
withSavedSession m = do
  saved_session <- getSession
  m `MC.finally` setSession saved_session

withTempSession :: CslMonad m => (CsEnv -> CsEnv) -> m a -> m a
withTempSession f m = withSavedSession $ modifySession f >> m

----------------------------------------
-- Logging
----------------------------------------

modifyLogger :: CslMonad m => (Logger -> Logger) -> m ()
modifyLogger f = modifySession $ \cs_env ->
  cs_env { cs_logger = f (cs_logger cs_env) }

pushLogHookM :: CslMonad m => (LogAction -> LogAction) -> m ()
pushLogHookM = modifyLogger . pushLogHook

popLogHookM :: CslMonad m => m ()
popLogHookM = modifyLogger popLogHook

putMsgM :: CslMonad m => SDoc -> m ()
putMsgM doc = do
  logger <- getLogger
  liftIO $ putMsg logger doc

putLogMsgM :: CslMonad m => MessageClass -> SrcSpan -> SDoc -> m ()
putLogMsgM msg_class loc doc = do
  logger <- getLogger
  liftIO $ logMsg logger msg_class loc doc

withTimingM :: CslMonad m => SDoc -> (b -> ()) -> m b -> m b
withTimingM doc force action = do
  logger <- getLogger
  withTiming logger doc force action

logDiagnostics :: CslMonad m => Messages CsMessage -> m ()
logDiagnostics warns = do
  dflags <- getSessionDynFlags
  logger <- getLogger
  let !diag_opts = initDiagOpts dflags
      !print_config = initPrintConfig dflags
  liftIO $ printOrThrowDiagnostics logger print_config diag_opts warns

newtype Csl a = Csl { unCs :: Session -> IO a }
  deriving stock (Functor)
  deriving (Applicative, Monad, MonadFail, MonadFix, MonadThrow, MonadCatch, MonadMask, MonadIO)
  via (ReaderT Session IO)

data Session = Session !(IORef CsEnv)

instance HasDynFlags Csl where
  getDynFlags = getSessionDynFlags

instance HasLogger Csl where
  getLogger = cs_logger <$> getSession

instance CslMonad Csl where
  getSession = Csl $ \(Session r) -> readIORef r
  setSession s' = Csl $ \(Session r) -> writeIORef r s'

reflectCs :: Csl a -> Session -> IO a
reflectCs m = unCs m

reifyCs :: (Session -> IO a) -> Csl a
reifyCs act = Csl $ act

printException :: (HasLogger m, MonadIO m, HasDynFlags m) => SourceError -> m ()
printException err = do
  dflags <- getDynFlags
  logger <- getLogger
  let !diag_opts = initDiagOpts dflags
      !print_config = initPrintConfig dflags
  liftIO $ printMessages logger print_config diag_opts (srcErrorMessages err)

type WarnErrLogger = forall m. (HasDynFlags m, MonadIO m, HasLogger m) => Maybe SourceError -> m ()

defaultWarnErrLogger :: WarnErrLogger
defaultWarnErrLogger Nothing = return ()
defaultWarnErrLogger (Just e) = printException e
