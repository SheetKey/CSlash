module CSlash.Utils.GlobalVars where

import GHC.Conc.Sync ( sharedCAF )

import System.IO.Unsafe
import Data.IORef
import Foreign (Ptr)

{-# NOINLINE v_unsafeHasPprDebug #-}
v_unsafeHasPprDebug :: IORef Bool
v_unsafeHasPprDebug = global False

{-# NOINLINE v_unsafeHasNoDebugOutput #-}
v_unsafeHasNoDebugOutput :: IORef Bool
v_unsafeHasNoDebugOutput = global False

{-# NOINLINE v_unsafeHasNoStateHack #-}
v_unsafeHasNoStateHack :: IORef Bool
v_unsafeHasNoStateHack = global False

unsafeHasPprDebug :: Bool
unsafeHasPprDebug = unsafePerformIO $ readIORef v_unsafeHasPprDebug

unsafeHasNoDebugOutput :: Bool
unsafeHasNoDebugOutput = unsafePerformIO $ readIORef v_unsafeHasNoDebugOutput

unsafeHasNoStateHack :: Bool
unsafeHasNoStateHack = unsafePerformIO $ readIORef v_unsafeHasNoStateHack

global :: a -> IORef a
global a = unsafePerformIO (newIORef a)
