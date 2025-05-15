{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}

module CSlash.Utils.Panic
  ( module CSlash.Utils.Panic
  , module CSlash.Utils.Panic.Plain
  , Exception.Exception(..)
  ) where

import CSlash.Stack

import CSlash.Utils.Outputable
import CSlash.Utils.Panic.Plain
import CSlash.Utils.Constants

import CSlash.Utils.Exception as Exception

import Control.Monad.IO.Class
import qualified Control.Monad.Catch as MC
import Control.Concurrent
import Data.Typeable ( cast )
import System.IO.Unsafe

import System.Posix.Signals as S

import System.Mem.Weak (deRefWeak)

data CsException
  = Signal Int
  | UsageError String
  | CmdLineError String
  | Panic String
  | PprPanic String SDoc
  | Sorry String
  | PprSorry String SDoc
  | InstallationError String
  | ProgramError String
  | PprProgramError String SDoc

instance Exception CsException where
  fromException (SomeException e)
    | Just ge <- cast e = Just ge
    | Just pge <- cast e = Just $
      case pge of
        PlainSignal n -> Signal n
        PlainUsageError str -> UsageError str
        PlainCmdLineError str -> CmdLineError str
        PlainPanic str -> Panic str
        PlainSorry str -> Sorry str
        PlainInstallationError str -> InstallationError str
        PlainProgramError str -> ProgramError str
    | otherwise = Nothing
  displayException exc = showCsExceptionUnsafe exc ""

instance Show CsException where
  showsPrec _ e = showCsExceptionUnsafe e

showCsExceptionUnsafe :: CsException -> ShowS
showCsExceptionUnsafe = showCsException defaultSDocContext

showCsException :: SDocContext -> CsException -> ShowS
showCsException ctx = showPlainCsException . \case
  Signal n -> PlainSignal n
  UsageError str -> PlainUsageError str
  CmdLineError str -> PlainCmdLineError str
  Panic str -> PlainPanic str
  Sorry str -> PlainSorry str
  InstallationError str -> PlainInstallationError str
  ProgramError str -> PlainProgramError str

  PprPanic str sdoc -> PlainPanic $
      concat [str, "\n\n", renderWithContext ctx sdoc]
  PprSorry str sdoc -> PlainProgramError $
      concat [str, "\n\n", renderWithContext ctx sdoc]
  PprProgramError str sdoc -> PlainProgramError $
      concat [str, "\n\n", renderWithContext ctx sdoc]

throwCsException :: CsException -> a
throwCsException = Exception.throw

throwCsExceptionIO :: CsException -> IO a
throwCsExceptionIO = Exception.throwIO

handleCsException :: ExceptionMonad m => (CsException -> m a) -> m a -> m a
handleCsException = MC.handle

pprPanic :: HasCallStack => String -> SDoc -> a
pprPanic s doc = panicDoc s (doc $$ callStackDoc)

panicDoc :: String -> SDoc -> a
panicDoc x doc = throwCsException (PprPanic x doc)

tryMost :: IO a -> IO (Either SomeException a)
tryMost action = do
  r <- try action
  case r of
    Left se -> case fromException se of
                 Just (Signal _) -> throwIO se
                 Just (Panic _) -> throwIO se
                 Just _ -> return $ Left se
                 Nothing -> case fromException se of
                              Just (_ :: IOException) -> return $ Left se
                              Nothing -> throwIO se
    Right v -> return (Right v)

{-# NOINLINE signalHandlersRefCount #-}
signalHandlersRefCount :: MVar (Word, Maybe (S.Handler, S.Handler, S.Handler, S.Handler))
signalHandlersRefCount = unsafePerformIO $ newMVar (0, Nothing)

withSignalHandlers :: ExceptionMonad m => m a -> m a
withSignalHandlers act = do
  main_thread <- liftIO myThreadId
  wtid <- liftIO (mkWeakThreadId main_thread)

  let interrupt = do
        r <- deRefWeak wtid
        case r of
          Nothing -> return ()
          Just t -> throwTo t UserInterrupt

  let installHandlers = do
        let installHandler' a b = installHandler a b Nothing
        hdlQUIT <- installHandler' sigQUIT (Catch interrupt)
        hdlINT <- installHandler' sigINT (Catch interrupt)
        let fatal_signal n = throwTo main_thread (Signal (fromIntegral n))
        hdlHUP <- installHandler' sigHUP (Catch (fatal_signal sigHUP))
        hdlTERM <- installHandler' sigTERM (Catch (fatal_signal sigTERM))
        return (hdlQUIT, hdlINT, hdlHUP, hdlTERM)

  let uninstallHandlers (hdlQUIT, hdlINT, hdlHUP, hdlTERM) = do
        _ <- installHandler sigQUIT hdlQUIT Nothing
        _ <- installHandler sigINT hdlINT Nothing
        _ <- installHandler sigHUP hdlHUP Nothing
        _ <- installHandler sigTERM hdlTERM Nothing
        return ()

  let mayInstallHandlers = liftIO $ modifyMVar_ signalHandlersRefCount $ \case
        (0, Nothing) -> do
          hdls <- installHandlers
          return (1, Just hdls)
        (c, oldHandlers) -> return (c+1, oldHandlers)

  let mayUninstallHandlers = liftIO $ modifyMVar_ signalHandlersRefCount $ \case
        (1, Just hdls) -> do
          _ <- uninstallHandlers hdls
          return (0, Nothing)
        (c, oldHandlers) -> return (c-1, oldHandlers)

  mayInstallHandlers
  act `MC.finally` mayUninstallHandlers

callStackDoc :: HasCallStack => SDoc
callStackDoc = prettyCallStackDoc callStack

prettyCallStackDoc :: CallStack -> SDoc
prettyCallStackDoc cs =
  hang (text "Call stack:")
       4 (vcat $ map text $ lines (prettyCallStack cs))

assertPprPanic :: HasCallStack => SDoc -> a
assertPprPanic msg = withFrozenCallStack (pprPanic "ASSERT failed!" msg)

assertPpr :: HasCallStack => Bool -> SDoc -> a -> a
{-# INLINE assertPpr #-}
assertPpr cond msg a =
  if debugIsOn && not cond
  then withFrozenCallStack (assertPprPanic msg)
  else a

massertPpr :: (HasCallStack, Applicative m) => Bool -> SDoc -> m ()
{-# INLINE massertPpr #-}
massertPpr cond msg = withFrozenCallStack (assertPpr cond msg (pure ()))

assertPprM :: (HasCallStack, Monad m) => m Bool -> SDoc -> m ()
{-# INLINE assertPprM #-}
assertPprM mcond msg = withFrozenCallStack (mcond >>= \cond -> massertPpr cond msg)
