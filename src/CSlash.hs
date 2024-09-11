{-# LANGUAGE ScopedTypeVariables #-}

module CSlash
  ( defaultErrorHandler
  ) where

import CSlash.Platform
import CSlash.Platform.Ways

-- import GHC.Driver.Phases   ( Phase(..), isHaskellSrcFilename
--                            , isSourceFilename, startPhase )
import CSlash.Driver.Env
import CSlash.Driver.Errors
import CSlash.Driver.Errors.Types
-- import GHC.Driver.CmdLine
import CSlash.Driver.Session
import CSlash.Driver.Backend
-- import GHC.Driver.Config.Finder (initFinderOpts)
import CSlash.Driver.Config.Parser (initParserOpts)
-- import GHC.Driver.Config.Logger (initLogFlags)
-- import GHC.Driver.Config.StgToJS (initStgToJSConfig)
import CSlash.Driver.Config.Diagnostic
import CSlash.Driver.Main
-- import GHC.Driver.Make
-- import GHC.Driver.Hooks
-- import GHC.Driver.Monad
-- import GHC.Driver.Ppr

-- import GHC.ByteCode.Types
-- import qualified GHC.Linker.Loader as Loader
-- import GHC.Runtime.Loader
-- import GHC.Runtime.Eval
-- import GHC.Runtime.Interpreter
-- import GHC.Runtime.Context
-- import GHCi.RemoteTypes

import qualified CSlash.Parser as Parser
import CSlash.Parser.Lexer
import CSlash.Parser.Annotation
-- import CSlash.Parser.Utils

-- import GHC.Iface.Load        ( loadSysInterface )
import CSlash.Cs
-- import GHC.Builtin.Types.Prim ( alphaTyVars )
import CSlash.Data.StringBuffer
import CSlash.Data.FastString
-- import qualified GHC.LanguageExtensions as LangExt
-- import GHC.Rename.Names (renamePkgQual, renameRawPkgQual, gresFromAvails)

-- import GHC.Tc.Utils.Monad    ( finalSafeMode, fixSafeInstances, initIfaceTcRn )
-- import GHC.Tc.Types
-- import GHC.Tc.Utils.TcType
-- import GHC.Tc.Module
-- import GHC.Tc.Utils.Instantiate
-- import GHC.Tc.Instance.Family

import CSlash.Utils.TmpFs
import CSlash.Utils.Error
import CSlash.Utils.Exception
import CSlash.Utils.Monad
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Logger
import CSlash.Utils.Fingerprint

-- import GHC.Core.Predicate
import CSlash.Core.Type
import CSlash.Core.TyCon
-- import CSlash.Core.Type.Ppr   ( pprForAll )
-- import GHC.Core.Class
import CSlash.Core.DataCon
-- import GHC.Core.FamInstEnv ( FamInst, famInstEnvElts, orphNamesOfFamInst )
-- import GHC.Core.InstEnv
import CSlash.Core

import CSlash.Data.Maybe

import CSlash.Types.Id
import CSlash.Types.Name      hiding ( varName )
import CSlash.Types.Avail
import CSlash.Types.SrcLoc
-- import GHC.Types.TyThing.Ppr  ( pprFamInst )
-- import GHC.Types.Annotations
import CSlash.Types.Name.Set
import CSlash.Types.Name.Reader
import CSlash.Types.SourceError
-- import GHC.Types.SafeHaskell
import CSlash.Types.Error
import CSlash.Types.Fixity
import CSlash.Types.Target
import CSlash.Types.Basic
import CSlash.Types.TyThing
import CSlash.Types.Name.Env
-- import CSlash.Types.Name.Ppr
import CSlash.Types.TypeEnv
-- import GHC.Types.BreakInfo
import CSlash.Types.PkgQual

import CSlash.Unit
import CSlash.Unit.Env
import CSlash.Unit.External
-- import GHC.Unit.Finder
import CSlash.Unit.Module.ModIface
-- import GHC.Unit.Module.ModGuts
import CSlash.Unit.Module.ModDetails
import CSlash.Unit.Module.ModSummary
import CSlash.Unit.Module.Graph
import CSlash.Unit.Home.ModInfo

import Control.Applicative ((<|>))
import Control.Concurrent
import Control.Monad
import Control.Monad.Catch as MC
import Data.Foldable
import Data.IORef
import Data.List (isPrefixOf)
import Data.Typeable    ( Typeable )
import Data.Word        ( Word8 )

import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Sequence as Seq

import System.Directory
import System.Environment ( getEnv, getProgName )
import System.Exit      ( exitWith, ExitCode(..) )
import System.FilePath
import System.IO.Error  ( isDoesNotExistError )

{- *********************************************************************
*                                                                      *
           Initialisation: exception handlers
*                                                                      *
********************************************************************* -}

defaultErrorHandler
  :: (ExceptionMonad m)
  => FatalMessager -> FlushOut -> m a -> m a
defaultErrorHandler fm (FlushOut flushOut) inner =
  MC.handle (\exception -> liftIO $ do
                flushOut
                case fromException exception of
                  Just (ioe :: IOException) ->
                    fm (show ioe)
                  _ -> case fromException exception of
                         Just UserInterrupt ->
                           liftIO $ throwIO UserInterrupt
                         Just StackOverflow ->
                           fm "stack overflow"
                         _ -> case fromException exception of
                                Just (ex :: ExitCode) -> liftIO $ throwIO ex
                                _ -> fm (show (Panic (show exception)))
                exitWith (ExitFailure 1)
            ) $
  handleCsException (\cse -> liftIO $ do
                        flushOut
                        case cse of
                          Signal _ -> return ()
                          ProgramError _ -> fm (show cse)
                          CmdLineError _ -> fm ("<command line>: " ++ show cse)
                          _ -> do progName <- getProgName
                                  fm (progName ++ ": " ++ show cse)
                        exitWith (ExitFailure 1)
                    ) $
  inner
                                
