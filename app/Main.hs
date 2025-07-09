{-# LANGUAGE TupleSections #-}

module Main (main) where

import qualified CSlash as CSL
import CSlash ( parseTargetFiles, Csl, CslMonad(..), LoadHowMuch(..) )

import CSlash.Driver.Backend
import CSlash.Driver.CmdLine
import CSlash.Driver.Env
import CSlash.Driver.Errors
import CSlash.Driver.Errors.Types
import CSlash.Driver.Phases
import CSlash.Driver.Session
import CSlash.Driver.Ppr
import CSlash.Driver.Pipeline  ( oneShot, compileFile )
-- import CSlash.Driver.MakeFile  ( doMkDependCS )
-- import GHC.Driver.Backpack  ( doBackpack )
-- import GHC.Driver.Plugins
import CSlash.Driver.Config.Logger (initLogFlags)
import CSlash.Driver.Config.Diagnostic

import CSlash.Platform
import CSlash.Platform.Ways
-- import GHC.Platform.Host

-- #if defined(HAVE_INTERNAL_INTERPRETER)
-- import GHCi.UI              ( interactiveUI, ghciWelcomeMsg, defaultGhciSettings )
-- #endif

-- import GHC.Runtime.Loader   ( loadFrontendPlugin, initializeSessionPlugins )

import CSlash.Unit.Env
import CSlash.Unit (UnitId, homeUnitDepends)
import CSlash.Unit.Home.ModInfo (emptyHomePackageTable)
import CSlash.Unit.Module ( ModuleName, mkModuleName )
import CSlash.Unit.Module.ModIface
import CSlash.Unit.State  ( pprUnits, pprUnitsSimple )
import CSlash.Unit.Finder ( findImportedModule, FindResult(..) )
import qualified CSlash.Unit.State as State
-- import CSlash.Unit.Types  ( IsBootInterface(..) )

import CSlash.Types.Basic     ( failed )
import CSlash.Types.SrcLoc
import CSlash.Types.SourceError
import CSlash.Types.Unique.Supply
import CSlash.Types.PkgQual

import CSlash.Utils.Error
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Monad       ( liftIO, mapMaybeM )
import CSlash.Utils.Binary        ( openBinMem, put_ )
import CSlash.Utils.Logger

import CSlash.Settings.Config
import CSlash.Settings.Constants
import CSlash.Settings.IO

import CSlash.HandleEncoding
import CSlash.Data.FastString
import CSlash.SysTools.BaseDir

import CSlash.Iface.Load
-- import GHC.Iface.Recomp.Binary ( fingerprintBinMem )

-- import GHC.Tc.Utils.Monad      ( initIfaceCheck )
-- import GHC.Iface.Errors.Ppr

import System.IO
import System.Environment
import System.Exit
import System.FilePath
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.Except (throwE, runExceptT)
import Data.Char
import Data.List ( isPrefixOf, partition, intercalate, (\\) )
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe
import Prelude
import GHC.ResponseFile (expandResponse)
import Data.Bifunctor
import CSlash.Data.Graph.Directed
import qualified Data.List.NonEmpty as NE

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  hSetBuffering stderr LineBuffering

  configureHandleEncoding
  
  CSL.defaultErrorHandler defaultFatalMessager defaultFlushOut $ do
    argv0 <- getArgs

    let (minusB_args, argv1) = partition ("-B" `isPrefixOf`) argv0
        mbMinusB | null minusB_args = Nothing
                 | otherwise = Just (drop 2 (last minusB_args))

        argv2 = map (mkGeneralLocated "on the commandline") argv1

    (mode, units, argv3, flagWarnings) <- parseModeFlags argv2

    case mode of
      Left preStartupMode ->
        case preStartupMode of
          ShowVersion -> showVersion
          ShowNumVersion -> putStrLn cProjectVersion
          ShowOptions -> showOptions
      Right postStartupMode -> CSL.runCsl mbMinusB $ do
        dflags <- CSL.getSessionDynFlags
        case postStartupMode of
          Left preLoadMode -> liftIO $ case preLoadMode of
                                         ShowInfo -> showInfo dflags
                                         ShowCslUsage -> showCslUsage dflags
                                         PrintWithDynFlags f -> putStrLn (f dflags)
          Right postLoadMode ->
            main' postLoadMode units dflags argv3 flagWarnings

main' :: PostLoadMode -> [String] -> DynFlags -> [Located String] -> [Warn] -> Csl ()
main' postLoadMode units dflags0 args flagWarnings = do
  let dflt_backend = backend dflags0
      (mode, bcknd, link) = case postLoadMode of
        DoMake -> (CompManager, dflt_backend, LinkBinary)
        DoMkDepend -> (MkDepend, dflt_backend, LinkBinary)
        DoAbiHash -> (OneShot, dflt_backend, LinkBinary)
        _ -> (OneShot, dflt_backend, LinkBinary)

  let dflags1 = dflags0 { csMode = mode
                        , backend = bcknd
                        , csLink = link
                        , verbosity = case postLoadMode of
                                        _ -> 1
                        }

  logger1 <- getLogger
  let logger2 = setLogFlags logger1 (initLogFlags dflags1)

  (dflags4, fileish_args, dynamicFlagWarnings) <-
    CSL.parseDynamicFlags logger2 dflags1 args

  let logger4 = setLogFlags logger2 (initLogFlags dflags4)

  CSL.prettyPrintCsErrors logger4 $ do
    let diag_opts = initDiagOpts dflags4
        flagWarnings' = CsDriverMessage <$> mconcat
          [warnsToMessages diag_opts flagWarnings, dynamicFlagWarnings]

    handleSourceError (\e -> do
                          CSL.printException e
                          liftIO $ exitWith (ExitFailure 1)) 
      (liftIO $ printOrThrowDiagnostics logger4 (initPrintConfig dflags4) diag_opts flagWarnings')

    liftIO $ showBanner postLoadMode dflags4
       
    let (dflags5, srcs, objs) = parseTargetFiles dflags4 (map unLoc fileish_args)

    -- TEMP
    cs_env <- getSession

    liftIO $ debugTraceMsg logger4 0 $ text "WHAT"

    liftIO $ debugTraceMsg logger4 0 $ vcat [ text "Debug package db first"
                                            , ppr $ ue_home_unit_graph $ cs_unit_env cs_env ]
    -- TEPM

    _ <- CSL.setSessionDynFlags dflags5
    dflags6 <- CSL.getSessionDynFlags

    liftIO $ initUniqSupply (initialUnique dflags6) (uniqueIncrement dflags6)

    cs_env <- getSession
    logger <- getLogger

    liftIO $ debugTraceMsg logger 2 $ vcat [ text "Debug package db last"
                                           , ppr $ ue_home_unit_graph $ cs_unit_env cs_env ]

    case verbosity dflags6 of
      v | v == 4 -> liftIO $ dumpUnitsSimple cs_env
        | v >= 5 -> liftIO $ dumpUnits cs_env
        | otherwise -> return ()

    liftIO $ checkOptions postLoadMode dflags6 srcs objs units

    handleSourceError
      (\e -> do
          CSL.printException e
          liftIO $ exitWith (ExitFailure 1)) $
      case postLoadMode of
        ShowInterface f ->
          liftIO $ showIface logger
                             (cs_dflags cs_env)
                             (cs_units cs_env)
                             (cs_NC cs_env)
                             f
        DoMake -> doMake units srcs
        DoMkDepend -> panic "doMkDependCS not implemented" --doMkDependCS (map fst srcs)
        StopBefore p -> liftIO (oneShot cs_env p srcs)
        DoAbiHash -> abiHash (map fst srcs)
        ShowPackages -> liftIO $ showUnits cs_env
    liftIO $ dumpFinalStats logger

-- -----------------------------------------------------------------------------
-- Option sanity checks

checkOptions
  :: PostLoadMode -> DynFlags -> [(String, Maybe Phase)] -> [String] -> [String] -> IO ()
checkOptions mode dflags srcs objs units = do
  let unknown_opts = [ f | (f@('-':_), _) <- srcs ]
  when (notNull unknown_opts) (unknownFlagsErr unknown_opts)
  
  if (isJust (outputHi dflags)
     && (isCompManagerMode mode || srcs `lengthExceeds` 1))
    then throwCsException
         (UsageError "-ohi can only be used when compiling a single source file")
    else
    if (isJust (dynOutputHi dflags)
       && (isCompManagerMode mode || srcs `lengthExceeds` 1))
    then throwCsException
         (UsageError "-dynohi can only be used when compiling a single source file")
    else
      if (srcs `lengthExceeds` 1 && isJust (outputFile dflags)
          && not (isLinkMode mode))
      then throwCsException
           (UsageError "can't apply -o to multiple source files")
      else
        do
          let not_linking = not (isLinkMode mode) || isNoLink (csLink dflags)
          when (not_linking && not (null objs)) $
            hPutStrLn stderr ("Warnings: the following files would be used as linker inputs, "
                              ++ "but linking is not being done: "
                              ++ unwords objs)

          if (null srcs && (null objs || not_linking)
              && needsInputsMode mode && null units)
            then throwCsException (UsageError "no input files")
            else return ()

-----------------------------------------------------------------------------
-- Cs modes of operation

type Mode = Either PreStartupMode PostStartupMode

type PostStartupMode = Either PreLoadMode PostLoadMode

data PreStartupMode
  = ShowVersion
  | ShowNumVersion
  | ShowOptions

showVersionMode :: Mode
showVersionMode = mkPreStartupMode ShowVersion

showNumVersionMode :: Mode
showNumVersionMode = mkPreStartupMode ShowNumVersion

showOptionsMode :: Mode
showOptionsMode = mkPreStartupMode ShowOptions

mkPreStartupMode :: PreStartupMode -> Mode
mkPreStartupMode = Left

isShowVersionMode :: Mode -> Bool
isShowVersionMode (Left ShowVersion) = True
isShowVersionMode _ = False

isShowNumVersionMode :: Mode -> Bool
isShowNumVersionMode (Left ShowNumVersion) = True
isShowNumVersionMode _ = False

data PreLoadMode
  = ShowCslUsage
  | ShowInfo
  | PrintWithDynFlags (DynFlags -> String)

showCslUsageMode :: Mode
showCslUsageMode = mkPreLoadMode ShowCslUsage

showInfoMode :: Mode
showInfoMode = mkPreLoadMode ShowInfo

printSetting :: String -> Mode
printSetting k = mkPreLoadMode (PrintWithDynFlags f)
  where f dflags = fromMaybe (panic ("Setting not found: " ++ show k))
                   $ lookup k (compilerInfo dflags)

mkPreLoadMode :: PreLoadMode -> Mode
mkPreLoadMode = Right . Left

isShowCslUsageMode :: Mode -> Bool
isShowCslUsageMode (Right (Left ShowCslUsage)) = True
isShowCslUsageMode _ = False

data PostLoadMode
  = ShowInterface FilePath
  | DoMkDepend
  | StopBefore StopPhase
  | DoMake
  | DoAbiHash
  | ShowPackages

doMkDependMode :: Mode
doMkDependMode = mkPostLoadMode DoMkDepend

doMakeMode :: Mode
doMakeMode = mkPostLoadMode DoMake

doAbiHashMode :: Mode
doAbiHashMode = mkPostLoadMode DoAbiHash

showUnitsMode :: Mode
showUnitsMode = mkPostLoadMode ShowPackages

showInterfaceMode :: FilePath -> Mode
showInterfaceMode fp = mkPostLoadMode (ShowInterface fp)

stopBeforeMode :: StopPhase -> Mode
stopBeforeMode phase = mkPostLoadMode (StopBefore phase)

mkPostLoadMode :: PostLoadMode -> Mode
mkPostLoadMode = Right . Right

isStopLnMode :: Mode -> Bool
isStopLnMode (Right (Right (StopBefore NoStop))) = True
isStopLnMode _ = False

isDoMakeMode :: Mode -> Bool
isDoMakeMode (Right (Right DoMake)) = True
isDoMakeMode _ = False

needsInputsMode :: PostLoadMode -> Bool
needsInputsMode DoMkDepend = True
needsInputsMode (StopBefore _) = True
needsInputsMode DoMake = True
needsInputsMode _ = False

isLinkMode :: PostLoadMode -> Bool
isLinkMode (StopBefore NoStop) = True
isLinkMode DoMake = True
isLinkMode _ = False

isCompManagerMode :: PostLoadMode -> Bool
isCompManagerMode DoMake = True
isCompManagerMode _ = False

-- -----------------------------------------------------------------------------
-- Parsing the mode flag

parseModeFlags :: [Located String] -> IO (Mode, [String], [Located String], [Warn])
parseModeFlags args = do
  ((leftover, errs1, warns), (mModeFlag, units, errs2, flags')) <-
    processCmdLineP mode_flags (Nothing, [], [], []) args

  let mode = case mModeFlag of
               Nothing -> doMakeMode
               Just (m, _) -> m

  unless (null errs1 && null errs2) $ throwCsException $ errorsToCsException $
    map (("on the commandline", )) $ map (unLoc . errMsg) errs1 ++ errs2

  return (mode, units, flags' ++ leftover, warns)

type ModeM = CmdLineP (Maybe (Mode, String), [String], [String], [Located String])

mode_flags :: [Flag ModeM]
mode_flags =
  [ defFlag "?" (PassFlag (setMode showCslUsageMode))
  , defFlag "-help" (PassFlag (setMode showCslUsageMode))
  , defFlag "V" (PassFlag (setMode showVersionMode))
  , defFlag "-version" (PassFlag (setMode showVersionMode))
  , defFlag "-numeric-version" (PassFlag (setMode showNumVersionMode))
  , defFlag "-info" (PassFlag (setMode showInfoMode))
  , defFlag "-show-options" (PassFlag (setMode showOptionsMode))
  , defFlag "-show-packages" (PassFlag (setMode showUnitsMode))
  ] ++
  [ defFlag k' (PassFlag (setMode (printSetting k)))
  | k <- [ "Project version"
         , "Project Git commit id"
         , "Booter version"
         , "Stage"
         , "Build platform"
         , "Host platform"
         , "Target platform"
         , "Object splitting supported"
         , "Support SMP"
         , "Unregisterised"
         , "Tabled next to code"
         , "RTS ways"
         , "Leading underscore"
         , "Debug on"
         , "LibDir"
         , "Global Package DB"
         , "C compiler link flags"
         ]
  , let k' = "-print-" ++ map (replaceSpace . toLower) k
        replaceSpace ' ' = '-'
        replaceSpace c = c
  ] ++
  [ defFlag "-show-iface" (HasArg (\f -> setMode (showInterfaceMode f)
                                         "--show-iface"))

  , defFlag "c" (PassFlag (\f -> do setMode (stopBeforeMode NoStop) f
                                    addFlag "-no-link" f))
  , defFlag "M" (PassFlag (setMode doMkDependMode))
  , defFlag "-make" (PassFlag (setMode doMakeMode))
  , defFlag "unit" (SepArg (\s -> addUnit s "-unit"))
  , defFlag "-abi-hash" (PassFlag (setMode doAbiHashMode))
  ]

addUnit :: String -> String -> EwM ModeM ()
addUnit unit_str _arg = liftEwM $ do
  (mModeFlag, units, errs, flags') <- getCmdLineState
  putCmdLineState (mModeFlag, unit_str:units, errs, flags')

setMode :: Mode -> String -> EwM ModeM ()
setMode newMode newFlag = liftEwM $ do
  (mModeFlag, units, errs, flags') <- getCmdLineState
  let (modeFlag', errs') =
        case mModeFlag of
          Nothing -> ((newMode, newFlag), errs)
          Just (oldMode, oldFlag)
            | isStopLnMode oldMode && isDoMakeMode newMode
              || isStopLnMode newMode && isDoMakeMode oldMode
              -> ((doMakeMode, "--make"), [])

            | isDominantFlag oldMode -> ((oldMode, oldFlag), [])
            | isDominantFlag newMode -> ((newMode, newFlag), [])

            | otherwise -> let err = flagMismatchErr oldFlag newFlag
                 in ((oldMode, oldFlag), err : errs)

  putCmdLineState (Just modeFlag', units, errs', flags')
  where
    isDominantFlag f = isShowCslUsageMode f ||
                       isShowVersionMode f ||
                       isShowNumVersionMode f

flagMismatchErr :: String -> String -> String
flagMismatchErr oldFlag newFlag
  = "cannot use `" ++ oldFlag ++ "' with `" ++ newFlag ++ "'"

addFlag :: String -> String -> EwM ModeM ()
addFlag s flag = liftEwM $ do
  (m, units, e, flags') <- getCmdLineState
  putCmdLineState (m, units, e, mkGeneralLocated loc s : flags')
    where loc = "addFlag by " ++ flag ++ " on the commandline"

-- ----------------------------------------------------------------------------
-- Run --make mode

doMake :: [String] -> [(String, Maybe Phase)] -> Csl ()
doMake units targets = do
  cs_srcs <- case NE.nonEmpty units of
    Just ne_units -> initMulti ne_units
    Nothing -> do
      s <- initMake targets
      return $ map (uncurry (, Nothing, )) s
  case cs_srcs of
    [] -> return ()
    _ -> do
      targets' <- mapM (\(src, uid, phase) -> CSL.guessTarget src uid phase) cs_srcs
      CSL.setTargets targets'
      ok_flag <- CSL.load LoadAllTargets
      when (failed ok_flag) (liftIO $ exitWith (ExitFailure 1))

initMake :: [(String, Maybe Phase)] -> Csl [(String, Maybe Phase)]
initMake srcs = do
  let (cs_srcs, non_cs_srcs) = partition isCsishTarget srcs

  cs_env <- CSL.getSession

  if (null cs_srcs)
    then liftIO (oneShot cs_env NoStop srcs) >> return []
    else do o_files <- mapMaybeM (\x -> liftIO $ compileFile cs_env NoStop x)
                                 non_cs_srcs
            dflags <- CSL.getSessionDynFlags
            let dflags' = dflags { ldInputs = map (FileOption "") o_files ++ ldInputs dflags }
            _ <- CSL.setSessionDynFlags dflags'
            return cs_srcs

removeRTS :: [String] -> [String]
removeRTS ("+RTS" : xs) =
  case dropWhile (/="-RTS") xs of
    [] -> []
    (_ : ys) -> removeRTS ys
removeRTS (y:ys) = y : removeRTS ys
removeRTS [] = []
    
initMulti :: NE.NonEmpty String -> Csl [(String, Maybe UnitId, Maybe Phase)]
initMulti unitArgsFiles = do
  panic "initMulti"
  cs_env <- CSL.getSession
  let logger = cs_logger cs_env
  initial_dflags <- CSL.getSessionDynFlags

  dynFlagsAndSrcs <- forM unitArgsFiles $ \f -> do
    when (verbosity initial_dflags > 2) (liftIO $ print f)
    args <- liftIO $ expandResponse [f]
    (dflags2, fileish_args, warns) <- parseDynamicFlagsCmdLine
                                      initial_dflags (map (mkGeneralLocated f) (removeRTS args))
    handleSourceError
      (\e -> do
          CSL.printException e
          liftIO $ exitWith (ExitFailure 1)
      ) $
      liftIO $ printOrThrowDiagnostics
        logger (initPrintConfig dflags2) (initDiagOpts dflags2) (CsDriverMessage <$> warns)

    let (dflags3, srcs, objs) = parseTargetFiles dflags2 (map unLoc fileish_args)
        dflags4 = offsetDynFlags dflags3

    let (cs_srcs, non_cs_srcs) = partition isCsishTarget srcs

    let dubious_cs_env = csSetFlags dflags4 cs_env

    if (null cs_srcs)
      then liftIO (oneShot dubious_cs_env NoStop srcs) >> return (dflags4, [])
      else do o_files <- mapMaybeM (\x -> liftIO $ compileFile dubious_cs_env NoStop x)
                                   non_cs_srcs
              let dflags5 = dflags4 { ldInputs = map (FileOption "") o_files ++ ldInputs dflags4 }

              liftIO $ checkOptions DoMake dflags5 srcs objs []

              pure (dflags5, cs_srcs)

  let unitDflags = NE.map fst dynFlagsAndSrcs
      srcs = NE.map (\(dflags, lsrcs) -> map (uncurry (, Just $ homeUnitId_ dflags, )) lsrcs)
                    dynFlagsAndSrcs
      (cs_srcs, _) = unzip (map (partition (\(file, _, phase) -> isCsishTarget (file, phase)))
                                (NE.toList srcs))

  checkDuplicateUnits initial_dflags (NE.toList (NE.zip unitArgsFiles unitDflags))

  let (initial_home_graph, mainUnitId) = createUnitEnvFromFlags unitDflags
      home_units = unitEnv_keys initial_home_graph

  home_unit_graph <- forM initial_home_graph $ \homeUnitEnv -> do
    let cached_unit_dbs = homeUnitEnv_unit_dbs homeUnitEnv
        hue_flags = homeUnitEnv_dflags homeUnitEnv
        dflags = homeUnitEnv_dflags homeUnitEnv
    (dbs, unit_state, home_unit, mconstants) <-
      liftIO $ State.initUnits logger hue_flags cached_unit_dbs home_units

    updated_dflags <- liftIO $ updatePlatformConstants dflags mconstants
    pure $ HomeUnitEnv
      { homeUnitEnv_units = unit_state
      , homeUnitEnv_unit_dbs = Just dbs
      , homeUnitEnv_dflags = updated_dflags
      , homeUnitEnv_hpt = emptyHomePackageTable
      , homeUnitEnv_home_unit = Just home_unit
      }

  checkUnitCycles initial_dflags home_unit_graph

  let dflags = homeUnitEnv_dflags $ unitEnv_lookup mainUnitId home_unit_graph
  unitEnv <- assertUnitEnvInvariant <$>
    (liftIO $ initUnitEnv mainUnitId home_unit_graph
                          (csNameVersion dflags) (targetPlatform dflags))
  let final_cs_env = cs_env { cs_unit_env = unitEnv }

  CSL.setSession final_cs_env

  if (null cs_srcs)
    then do
    liftIO $ hPutStrLn stderr $ "Multi Mode can not be used for one-shot mode."
    liftIO $ exitWith (ExitFailure 1)
    else return $ concat cs_srcs

checkUnitCycles :: DynFlags -> UnitEnvGraph HomeUnitEnv -> Csl ()
checkUnitCycles dflags graph = processSCCs sccs
  where
    mkNode :: (UnitId, HomeUnitEnv) -> Node UnitId UnitId
    mkNode (uid, hue) = DigraphNode uid uid (homeUnitDepends (homeUnitEnv_units hue))
    nodes = map mkNode (unitEnv_elts graph)

    sccs = stronglyConnCompFromEdgedVerticesOrd nodes

    processSCCs [] = return ()
    processSCCs (AcyclicSCC _ : other_sccs) = processSCCs other_sccs
    processSCCs (CyclicSCC uids : _)
      = throwCsException $ CmdLineError $ showSDoc dflags (cycle_err uids)

    cycle_err uids = hang (text "Units form a dependency cycle:") 2 (one_err uids)

    one_err uids = vcat $ (map (\uid -> text "-" <+> ppr uid <+> text "depends on") start)
                          ++ [text "-" <+> ppr final]
      where
        start = init uids
        final = last uids

checkDuplicateUnits :: DynFlags -> [(FilePath, DynFlags)] -> Csl ()
checkDuplicateUnits dflags flags =
  unless (null duplicate_ids)
         (throwCsException $ CmdLineError $ showSDoc dflags multi_err)
  where
    uids = map (second homeUnitId_) flags
    deduplicated_uids = ordNubOn snd uids
    duplicate_ids = Set.fromList (map snd uids \\ map snd deduplicated_uids)

    duplicate_flags = filter (flip Set.member duplicate_ids . snd) uids

    one_err (fp, home_uid) = text "-" <+> ppr home_uid <+> text "defined in" <+> text fp

    multi_err = hang (text "Multiple units with the same unit-id:") 2
                     (vcat (map one_err duplicate_flags))

offsetDynFlags :: DynFlags -> DynFlags
offsetDynFlags dflags =
  dflags { hiDir = c hiDir
         , objectDir = c objectDir
         , stubDir = c stubDir
         , hieDir = c hieDir
         , dumpDir = c dumpDir
         }
  where
    c f = augment_maybe (f dflags)

    augment_maybe Nothing = Nothing
    augment_maybe (Just f) = Just (augment f)

    augment f | isRelative f, Just offset <- workingDirectory dflags = offset </> f
              | otherwise = f

createUnitEnvFromFlags :: NE.NonEmpty DynFlags -> (HomeUnitGraph, UnitId)
createUnitEnvFromFlags unitDflags =
  let newInternalUnitEnv dflags = mkHomeUnitEnv dflags emptyHomePackageTable Nothing
      unitEnvList = NE.map (\dflags -> (homeUnitId_ dflags, newInternalUnitEnv dflags)) unitDflags
      activeUnit = fst $ NE.head unitEnvList
  in (unitEnv_new (Map.fromList (NE.toList (unitEnvList))), activeUnit)

-- ---------------------------------------------------------------------------
-- Various banners and verbosity output.

showBanner :: PostLoadMode -> DynFlags -> IO ()
showBanner _ dflags = do
  let verb = verbosity dflags
  when (verb >= 2) $ do
    hPutStr stderr "CSlash Compiler, Version "
    hPutStrLn stderr cProjectVersion

showInfo :: DynFlags -> IO ()
showInfo dflags =
  let sq x = " [" ++ x ++ "\n ]"
  in putStrLn $ sq $ intercalate "\n ," $ map show $ compilerInfo dflags

showVersion :: IO ()
showVersion = putStrLn (cProjectName ++ ", version " ++ cProjectVersion)

showOptions :: IO ()
showOptions = putStr (unlines availableOptions)
  where
    availableOptions = concat
                       [ flagsForCompletion
                       , map ('-':) (getFlagNames mode_flags)
                       ]
    getFlagNames opts = map flagName opts

showCslUsage :: DynFlags -> IO ()
showCslUsage dflags = do
  let usage_path = csUsagePath dflags
  usage <- readFile usage_path
  progName <- getProgName
  dump progName usage
  where
    dump progName xs = case xs of
      "" -> return ()
      '$':'$':s -> putStr progName >> dump progName s
      c:s -> putChar c >> dump progName s

dumpFinalStats :: Logger -> IO ()
dumpFinalStats logger = do
  when (logHasDumpFlag logger Opt_D_faststring_stats) $ dumpFastStringStats logger

  when (logHasDumpFlag logger Opt_D_dump_faststrings) $ do
    fss <- getFastStringTable
    let ppr_table = fmap ppr_segment (fss `zip` [0..])
        ppr_segment (s, n) = hang (text "Segment" <+> int n) 2
                                  (vcat (fmap ppr_bucket (s `zip` [0..])))
        ppr_bucket (b, n) = hang (text "Bucket" <+> int n) 2 (vcat (fmap ftext b))
    putDumpFileMaybe logger Opt_D_dump_faststrings "FastStrings" FormatText (vcat ppr_table)

dumpFastStringStats :: Logger -> IO ()
dumpFastStringStats logger = do
  segments <- getFastStringTable
  hasZ <- getFastStringZEncCounter
  let buckets = concat segments
      bucketsPerSegment = map length segments
      entriesPerBucket = map length buckets
      entries = sum entriesPerBucket
      msg = text "FastString stats:" $$ nest 4 (vcat
        [ text "segments:         " <+> int (length segments)
        , text "buckets:          " <+> int (sum bucketsPerSegment)
        , text "entries:          " <+> int entries
        , text "largest segment   " <+> int (maximum bucketsPerSegment)
        , text "smallest segment: " <+> int (minimum bucketsPerSegment)
        , text "longest bucket:   " <+> int (maximum entriesPerBucket)
        , text "has z-encoding:   " <+> (hasZ `pcntOf` entries)
        ])
  putMsg logger msg
  where
    x `pcntOf` y = int ((x * 100) `quot` y) Outputable.<> char '%'

showUnits :: CsEnv -> IO ()
showUnits cs_env = putStrLn (showSDoc (cs_dflags cs_env) (pprUnits (cs_units cs_env)))

dumpUnits :: CsEnv -> IO ()
dumpUnits cs_env = putMsg (cs_logger cs_env) (pprUnits (cs_units cs_env))

dumpUnitsSimple :: CsEnv -> IO ()
dumpUnitsSimple cs_env = putMsg (cs_logger cs_env) (pprUnitsSimple (cs_units cs_env))

-- -----------------------------------------------------------------------------
-- ABI hash support

abiHash :: [String] -> Csl ()
abiHash = panic "abiHash"

-- -----------------------------------------------------------------------------
-- Util

unknownFlagsErr :: [String] -> a
unknownFlagsErr fs = throwCsException $ UsageError $ concatMap oneError fs
  where
    oneError f =
      "unrecognised flag: " ++ f ++ "\n" ++
      (case flagSuggestions (nubSort allNonDeprecatedFlags) f of
         [] -> ""
         suggs -> "did you mean one of:\n" ++ unlines (map ("  " ++) suggs))
