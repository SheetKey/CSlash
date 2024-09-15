{-# LANGUAGE ScopedTypeVariables #-}

module CSlash
  ( defaultErrorHandler

  , Csl, CslMonad(..), CsEnv
  , runCsl
  , printException
  , handleSourceError

  , DynFlags(..), GeneralFlag(..), Severity(..), Backend, gopt
  , CsMode(..), CsLink(..)
  , parseTargetFiles

  , LoadHowMuch(..)
  ) where

import CSlash.Platform
import CSlash.Platform.Ways

import CSlash.Driver.Phases   ( Phase(..), isCsSrcFilename
                              , isSourceFilename, startPhase )
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
import CSlash.Driver.Make
-- import GHC.Driver.Hooks
import CSlash.Driver.Monad
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
                                
{- *********************************************************************
*                                                                      *
           The Csl Monad
*                                                                      *
********************************************************************* -}

runCsl :: Maybe FilePath -> Csl a -> IO a
runCsl mb_top_dir csl = do
  ref <- newIORef (panic "empty session")
  let session = Session ref
  flip unCsl session $ withSignalHandlers $ do
    initCslMonad mb_top_dir
    withCleanupSession csl

withCleanupSession :: CslMonad m => m a -> m a
withCleanupSession csl = csl `MC.finally` cleanup
  where
    cleanup = do
      cs_env <- getSession
      let dflags = cs_dflags cs_env
          logger = cs_logger cs_env
          tmpfs = cs_tmpfs cs_env
      liftIO $ do
        unless (gopt Opt_KeepTmpFiles dflags) $ do
          cleanTempFiles logger tmpfs
          cleanTempDirs logger tmpfs

initCslMonad :: CslMonad m => Maybe FilePath -> m ()
initCslMonad mb_top_dir = setSession =<< liftIO (initCsEnv mb_top_dir)

{- *********************************************************************
*                                                                      *
           Flags & settings
*                                                                      *
********************************************************************* -}

parseTargetFiles :: DynFlags -> [String] -> (DynFlags, [(String, Maybe Phase)], [String])
parseTargetFiles dflags0 fileish_args =
  let normal_fileish_paths = map normalise_hyp fileish_args
      (src, raw_objs) = partition_args normal_fileish_paths [] []
      objs = map (augmentByWorkingDirectory dflags0) raw_objs

      dflags1 = dflags0 { ldInputs = map (FileOption "") objs
                                     ++ ldInputs dflags0 }
  in (dflags1, src, objs)

-- -----------------------------------------------------------------------------

partition_args
  :: [String] -> [(String, Maybe Phase)] -> [String] -> ([(String, Maybe Phase)], [String])
partition_args [] srcs objs = (reverse srcs, reverse objs)
partition_args ("-x":suff:args) srcs objs
  | "none" <- suff = partition_args args srcs objs
  | StopLn <- phase = partition_args args srcs (slurp ++ objs)
  | otherwise = partition_args rest (these_srcs ++ srcs) objs
  where
    phase = startPhase suff
    (slurp, rest) = break (== "-x") args
    these_srcs = zip slurp (repeat (Just phase))
partition_args (arg:args) srcs objs
  | looks_like_an_input arg = partition_args args ((arg, Nothing):srcs) objs
  | otherwise = partition_args args srcs (arg:objs)

looks_like_an_input :: String -> Bool
looks_like_an_input m
  = isSourceFilename m
  || looksLikeModuleName m
  || "-" `isPrefixOf` m
  || not (hasExtension m)

normalise_hyp :: FilePath -> FilePath
normalise_hyp fp
  | strt_dot_sl && "-" `isPrefixOf` nfp = cur_dir ++ nfp
  | otherwise = nfp
  where
    strt_dot_sl = "./" `isPrefixOf` fp
    cur_dir = '.' : [pathSeparator]
    nfp = normalise fp
