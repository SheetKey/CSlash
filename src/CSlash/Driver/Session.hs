{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}

module CSlash.Driver.Session
  ( DumpFlag(..)
  , GeneralFlag(..)
  , WarningFlag(..)
  , FatalMessager, FlushOut(..)
  , hasPprDebug, hasNoDebugOutput, hasNoStateHack
  , dopt
  , gopt
  , wopt
  , DynFlags(..)
  , HasDynFlags(..), ContainsDynFlags(..)
  , CsMode(..)
  , CsLink(..)
  , Option(..), showOpt

  , Settings(..)

  , defaultDynFlags
  , initDynFlags
  , defaultFatalMessager
  , defaultFlushOut
  , augmentByWorkingDirectory

  , CmdLineP(..), runCmdLineP
  , getCmdLineState, putCmdLineState
  , processCmdLineP

  , compilerInfo

  , setUnsafeGlobalDynFlags
  ) where 

import CSlash.Platform
import CSlash.Platform.Ways
-- import CSlash.Platform.Profile

import CSlash.Unit.Types
-- import CSlash.Unit.Parser
import CSlash.Unit.Module
import CSlash.Unit.Module.Warnings
import CSlash.Driver.DynFlags
import CSlash.Driver.Config.Diagnostic
import CSlash.Driver.Flags
import CSlash.Driver.Backend
import CSlash.Driver.Errors.Types
-- import GHC.Driver.Plugins.External
import CSlash.Settings.Config
import CSlash.Core.Unfold
import CSlash.Driver.CmdLine
import CSlash.Utils.Panic
import CSlash.Utils.Misc
import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.GlobalVars
import CSlash.Data.Maybe
import CSlash.Data.Bool
import CSlash.Types.Error
import CSlash.Utils.Monad
import CSlash.Types.SrcLoc
-- import GHC.Types.SafeHaskell
import CSlash.Types.Basic ( treatZeroAsInf )
import CSlash.Data.FastString
import CSlash.Utils.TmpFs
import CSlash.Utils.Fingerprint
import CSlash.Utils.Outputable
import CSlash.Settings
-- import GHC.CmmToAsm.CFG.Weight
-- import GHC.Core.Opt.CallerCC

import CSlash.SysTools.BaseDir ( expandToolDir, expandTopDir )

import Data.IORef
import Control.Arrow ((&&&))
import Control.Monad
import Control.Monad.Trans.State as State
import Data.Functor.Identity

import Data.Ord
import Data.Char
import Data.List (intercalate, sortBy, partition)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Word
import System.FilePath
import Text.ParserCombinators.ReadP hiding (char)
import Text.ParserCombinators.ReadP as R

import qualified GHC.Data.EnumSet as EnumSet

-- import qualified GHC.LanguageExtensions as LangExt

{- *********************************************************************
*                                                                      *
                DynFlags parser
*                                                                      *
********************************************************************* -}

newtype CmdLineP s a = CmdLineP (forall m. (Monad m) => StateT s m a)
  deriving (Functor)

instance Applicative (CmdLineP s) where
  pure x = CmdLineP (pure x)
  (<*>) = ap

instance Monad (CmdLineP s) where
  CmdLineP k >>= f = CmdLineP (k >>= \x -> case f x of CmdLineP g -> g)
  return = pure

getCmdLineState :: CmdLineP s s
getCmdLineState = CmdLineP State.get

putCmdLineState :: s -> CmdLineP s ()
putCmdLineState x = CmdLineP (State.put x)

runCmdLineP :: CmdLineP s a -> s -> (a, s)
runCmdLineP (CmdLineP k) s0 = runIdentity $ runStateT k s0

processCmdLineP
  :: forall s m. MonadIO m
  => [Flag (CmdLineP s)]
  -> s
  -> [Located String]
  -> m (([Located String], [Err], [Warn]), s)
processCmdLineP activeFlags s0 args =
  runStateT (processArgs (map (hoistFlag getCmdLineP) activeFlags) args parseResponseFile) s0
  where
    getCmdLineP :: CmdLineP s a -> StateT s m a
    getCmdLineP (CmdLineP k) = k

augmentByWorkingDirectory :: DynFlags -> FilePath -> FilePath
augmentByWorkingDirectory dflags fp | isRelative fp, Just offset <- workingDirectory dflags
  = offset </> fp
augmentByWorkingDirectory _ fp = fp

-- -----------------------------------------------------------------------------
-- Compiler Info

compilerInfo :: DynFlags -> [(String, String)]
compilerInfo dflags
  = ("Project name", cProjectName)
  : map (fmap $ expandDirectories (topDir dflags) (toolDir dflags))
        (rawSettings dflags)
  ++ [ ("Project version", projectVersion dflags)
     , ("Project Git commit id", cProjectGitCommitId)
     , ("Project Version Int", cProjectVersionInt)
     , ("Project Unit Id", cProjectUnitId)

     , ("Object splitting supported", showBool False)
     , ("Support dynamic-too", showBool $ not isWindows)
     , ("Support reexported-modules", "YES")
     , ("Support thinning and renaming package flags", "YES")
     , ("Requires unified installed package IDs", "YES")
     , ("Uses unit IDs", "YES")
     , ("Debug on", showBool debugIsOn)
     , ("LibDir", topDir dflags)
     , ("Global Package DB", globalPackageDatabasePath dflags)
     ]
  where
    showBool True = "YES"
    showBool False = "NO"
    platform = targetPlatform dflags
    isWindows = False
    useInplaceMinGW = toolSettings_useInplaceMinGW $ toolSettings dflags
    expandDirectories :: FilePath -> Maybe FilePath -> String -> String
    expandDirectories topd mtoold = expandToolDir useInplaceMinGW mtoold . expandTopDir topd

setUnsafeGlobalDynFlags :: DynFlags -> IO ()
setUnsafeGlobalDynFlags dflags = do
  writeIORef v_unsafeHasPprDebug (hasPprDebug dflags)
  writeIORef v_unsafeHasNoDebugOutput (hasNoDebugOutput dflags)
  writeIORef v_unsafeHasNoStateHack (hasNoStateHack dflags)

