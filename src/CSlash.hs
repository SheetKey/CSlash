{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CSlash
  ( defaultErrorHandler
  , prettyPrintCsErrors

  , Csl, CslMonad(..), CsEnv
  , runCsl
  , printException
  , handleSourceError

  , DynFlags(..), GeneralFlag(..), Severity(..), Backend, gopt
  , CsMode(..), CsLink(..)
  , parseDynamicFlags, parseTargetFiles
  , getSessionDynFlags
  , setSessionDynFlags

  , Target(..), TargetId(..), Phase
  , setTargets
  , getTargets
  , addTarget
  , removeTarget
  , guessTarget

  , depanalE
  , load, loadWithCache, LoadHowMuch(..)
  , SuccessFlag(..), succeeded, failed
  ) where

import Prelude hiding ((<>))

import CSlash.Platform
import CSlash.Platform.Ways

import CSlash.Driver.Phases   ( Phase(..), isCsSrcFilename
                              , isSourceFilename, startPhase )
import CSlash.Driver.Env
import CSlash.Driver.Errors
import CSlash.Driver.Errors.Types
import CSlash.Driver.CmdLine
import CSlash.Driver.Session
import CSlash.Driver.Backend
import CSlash.Driver.Config.Finder (initFinderOpts)
import CSlash.Driver.Config.Parser (initParserOpts)
import CSlash.Driver.Config.Logger (initLogFlags)
-- import GHC.Driver.Config.StgToJS (initStgToJSConfig)
import CSlash.Driver.Config.Diagnostic
import CSlash.Driver.Main
import CSlash.Driver.Make
-- import GHC.Driver.Hooks
import CSlash.Driver.Monad
import CSlash.Driver.Ppr

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

import Debug.Trace (trace)

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

setSessionDynFlags :: (HasCallStack, CslMonad m) => DynFlags -> m ()
setSessionDynFlags dflags0 = do
  cs_env <- getSession
  logger <- getLogger
  dflags <- checkNewDynFlags logger dflags0
  let all_uids = cs_all_home_unit_ids cs_env
  case S.toList all_uids of
    [uid] -> do
      setUnitDynFlagsNoCheck uid dflags
      modifySession (csUpdateLoggerFlags . csSetActiveUnitId (homeUnitId_ dflags))
    [] -> panic "nohue"
    _ -> panic "setSessionDynFlags can only be used with a single home unit"

setUnitDynFlagsNoCheck :: CslMonad m => UnitId -> DynFlags -> m ()
setUnitDynFlagsNoCheck uid dflags1 = do
  logger <- getLogger
  cs_env <- getSession

  let old_hue = ue_findHomeUnitEnv uid (cs_unit_env cs_env)
      cached_unit_dbs = homeUnitEnv_unit_dbs old_hue
  (dbs, unit_state, home_unit, mconstants) <- liftIO $
    initUnits logger dflags1 cached_unit_dbs (cs_all_home_unit_ids cs_env)
  updated_dflags <- liftIO $ updatePlatformConstants dflags1 mconstants

  let upd hue = hue { homeUnitEnv_units = unit_state
                    , homeUnitEnv_unit_dbs = Just dbs
                    , homeUnitEnv_dflags = updated_dflags
                    , homeUnitEnv_home_unit = Just home_unit
                    }

      unit_env = ue_updateHomeUnitEnv upd uid (cs_unit_env cs_env)

      dflags = updated_dflags

      unit_env0 = unit_env { ue_platform = targetPlatform dflags
                           , ue_namever = csNameVersion dflags
                           }

      !unit_env1 = if homeUnitId_ dflags /= uid
                   then ue_renameUnitId uid (homeUnitId_ dflags) unit_env0
                   else unit_env0

  modifySession $ \h -> h { cs_unit_env = unit_env1 }

  invalidateModSummaryCache

invalidateModSummaryCache :: CslMonad m => m ()
invalidateModSummaryCache = modifySession $ \h -> h { cs_mod_graph = mapMG inval (cs_mod_graph h) }
  where
    inval ms = ms { ms_cs_hash = fingerprint0 }

parseDynamicFlags
  :: MonadIO m
  => Logger
  -> DynFlags
  -> [Located String]
  -> m (DynFlags, [Located String], Messages DriverMessage)
parseDynamicFlags logger dflags cmdline = do
  (dflags1, leftovers, warns) <- parseDynamicFlagsCmdLine dflags cmdline
  let logger1 = setLogFlags logger (initLogFlags dflags1)
  dflags2 <- liftIO $ interpretPackageEnv logger1 dflags1
  return (dflags2, leftovers, warns)

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

-----------------------------------------------------------------------------

checkNewDynFlags :: MonadIO m => Logger -> DynFlags -> m DynFlags
checkNewDynFlags logger dflags = do
  let (dflags', warnings) = makeDynFlagsConsistent dflags
      diag_opts = initDiagOpts dflags
      print_config = initPrintConfig dflags
  liftIO $ printOrThrowDiagnostics logger print_config diag_opts
    $ fmap CsDriverMessage $ warnsToMessages diag_opts warnings
  return dflags'

{- *********************************************************************
*                                                                      *
           Setting, getting, and modifying the targets
*                                                                      *
********************************************************************* -}

setTargets :: CslMonad m => [Target] -> m ()
setTargets targets = modifySession $ \h -> h { cs_targets = targets }

getTargets :: CslMonad m => m [Target]
getTargets = withSession (return . cs_targets)

addTarget :: CslMonad m => Target -> m ()
addTarget target = modifySession $ \h -> h { cs_targets = target : cs_targets h }

removeTarget :: CslMonad m => TargetId -> m ()
removeTarget target_id = modifySession $ \h -> h { cs_targets = filter (cs_targets h) }
  where
    filter targets = [ t | t@Target { targetId = id } <- targets, id /= target_id ]

guessTarget :: CslMonad m => String -> Maybe UnitId -> Maybe Phase -> m Target
guessTarget str mUnitId (Just phase) = do
  tuid <- unitIdOrHomeUnit mUnitId
  return (Target (TargetFile str (Just phase)) True tuid Nothing)
guessTarget str mUnitId Nothing
  | isCsSrcFilename file
  = target (TargetFile file Nothing)
  | otherwise = do
      exists <- liftIO $ doesFileExist cs_file
      if | exists -> target (TargetFile cs_file Nothing)
         | looksLikeModuleName file -> trace "guessTarget TargetModule" $
                                       target (TargetModule (mkModuleName file))
         | otherwise -> do
             dflags <- getDynFlags
             liftIO $ throwCsExceptionIO
                      (ProgramError (showSDoc dflags
                                     $ text "target" <+> quotes (text file)
                                     <+> text "is not a module name or a source file"))
  where
    (file, obj_allowed)
      | '*' : rest <- str = (rest, False)
      | otherwise = (str, True)
    cs_file = file <.> "cs"
    target tid = do
      tuid <- unitIdOrHomeUnit mUnitId
      pure $ Target tid obj_allowed tuid Nothing

unitIdOrHomeUnit :: CslMonad m => Maybe UnitId -> m UnitId
unitIdOrHomeUnit mUnitId = do
  currentHomeUnitId <- homeUnitId . cs_home_unit <$> getSession
  pure (fromMaybe currentHomeUnitId mUnitId)

-- -----------------------------------------------------------------------------
-- Find the package environment (if one exists)

interpretPackageEnv :: Logger -> DynFlags -> IO DynFlags
interpretPackageEnv logger dflags = do
  mPkgEnv <- runMaybeT $ msum $
              [ getCmdLineArg >>= \ env -> msum
                [ probeNullEnv env
                , probeEnvFile env
                , probeEnvName env
                , cmdLineError env
                ]
              , getEnvVar >>= \ env -> msum
                [ probeNullEnv env
                , probeEnvFile env
                , probeEnvName env
                , envError env
                ]
              , notIfHideAllPackages >> msum
                [ findLocalEnvFile >>= probeEnvFile
                , probeEnvName defaultEnvName
                ]
              ]
  case mPkgEnv of
    Nothing -> return dflags
    Just "-" -> return dflags
    Just envfile -> do
      content <- readFile envfile
      compilationProgressMsg logger (text "Loaded package environment from " <> text envfile)
      let (_, dflags') = runCmdLineP (runEwM (setFlagsFromEnvFile envfile content)) dflags
      return dflags'
  where
    archOS = platformArchOS (targetPlatform dflags)

    namedEnvPath :: String -> MaybeT IO FilePath
    namedEnvPath name = do
      appdir <- versionedAppDir (programName dflags) archOS
      return $ appdir </> "environments" </> name

    probeEnvName :: String -> MaybeT IO FilePath
    probeEnvName name = probeEnvFile =<< namedEnvPath name

    probeEnvFile :: FilePath -> MaybeT IO FilePath
    probeEnvFile path = do
      guard =<< liftMaybeT (doesFileExist path)
      return path

    probeNullEnv :: FilePath -> MaybeT IO FilePath
    probeNullEnv "-" = return "-"
    probeNullEnv _ = mzero

    getCmdLineArg :: MaybeT IO String
    getCmdLineArg = MaybeT $ return $ packageEnv dflags

    getEnvVar :: MaybeT IO String
    getEnvVar = do
      mvar <- liftMaybeT $ MC.try $ getEnv "CSL_ENVIRONMENT"
      case mvar of
        Right var -> return var
        Left err -> if isDoesNotExistError err
                    then mzero
                    else liftMaybeT $ throwIO err

    notIfHideAllPackages :: MaybeT IO ()
    notIfHideAllPackages =
      guard (not (gopt Opt_HideAllPackages dflags))

    defaultEnvName :: String
    defaultEnvName = "default"

    localEnvFileName :: FilePath
    localEnvFileName = ".csl.environment" <.> versionedFilePath archOS

    findLocalEnvFile :: MaybeT IO FilePath
    findLocalEnvFile = do
      curdir <- liftMaybeT getCurrentDirectory
      homedir <- tryMaybeT getHomeDirectory
      let probe dir | isDrive dir || dir == homedir = mzero
          probe dir = do
            let file = dir </> localEnvFileName
            exists <- liftMaybeT (doesFileExist file)
            if exists
              then return file
              else probe (takeDirectory dir)

      probe curdir

    cmdLineError :: String -> MaybeT IO a
    cmdLineError env = liftMaybeT . throwCsExceptionIO . CmdLineError $
      "Package environment " ++ show env ++ " not found"

    envError :: String -> MaybeT IO a
    envError env = liftMaybeT . throwCsExceptionIO . CmdLineError $
      "Package environment "
      ++ show env
      ++ " (specified in CSL_ENVIRONMENT) not found"
