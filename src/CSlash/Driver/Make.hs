{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Driver.Make where

import Prelude hiding ((<>))

import CSlash.Platform

-- import GHC.Tc.Utils.Backpack
import GHC.Tc.Utils.Monad  ( initIfaceCheck{-, concatMapM-} )

-- import GHC.Runtime.Interpreter
-- import qualified GHC.Linker.Loader as Linker
import CSlash.Linker.Types

import CSlash.Platform.Ways

import CSlash.Driver.Config.Finder (initFinderOpts)
import CSlash.Driver.Config.Parser (initParserOpts)
import CSlash.Driver.Config.Diagnostic
import CSlash.Driver.Phases
import CSlash.Driver.Pipeline
import CSlash.Driver.Session
import CSlash.Driver.Backend
import CSlash.Driver.Monad
import CSlash.Driver.Env
import CSlash.Driver.Errors
import CSlash.Driver.Errors.Types
import CSlash.Driver.Main hiding (logDiagnostics)
import CSlash.Driver.MakeSem

import CSlash.Parser.Header

-- import GHC.Iface.Load      ( cannotFindModule )
-- import GHC.IfaceToCore     ( typecheckIface )
import CSlash.Iface.Recomp    ( RecompileRequired(..), CompileReason(..) )

import CSlash.Data.Bag        ( listToBag, emptyBag )
import CSlash.Data.Graph.Directed
import CSlash.Data.FastString
import CSlash.Data.Maybe      ( expectJust )
import CSlash.Data.StringBuffer
-- import qualified GHC.LanguageExtensions as LangExt

import CSlash.Utils.Exception ( throwIO, SomeAsyncException )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc
import CSlash.Utils.Error
import CSlash.Utils.Logger
import CSlash.Utils.Fingerprint
import CSlash.Utils.TmpFs

import CSlash.Types.Basic
import CSlash.Types.Error
import CSlash.Types.Target
import CSlash.Types.SourceFile
import CSlash.Types.SourceError
import CSlash.Types.SrcLoc
import CSlash.Types.Unique.Map
import CSlash.Types.PkgQual

import CSlash.Unit
import CSlash.Unit.Env
import CSlash.Unit.Finder
import CSlash.Unit.Module.ModSummary
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.Graph
import CSlash.Unit.Home.ModInfo
import CSlash.Unit.Module.ModDetails

import Data.Either ( rights, partitionEithers, lefts )
import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Concurrent ( newQSem, waitQSem, signalQSem, ThreadId, killThread, forkIOWithUnmask )
import qualified GHC.Conc as CC
import Control.Concurrent.MVar
import Control.Monad
import Control.Monad.Trans.Except ( ExceptT(..), runExceptT, throwE )
import qualified Control.Monad.Catch as MC
import Data.IORef
import Data.Maybe
import Data.Time
import Data.List (sortOn)
import Data.Bifunctor (first)
import System.Directory
import System.FilePath
import System.IO        ( fixIO )

import GHC.Conc ( getNumProcessors, getNumCapabilities, setNumCapabilities )
import Control.Monad.IO.Class
import Control.Monad.Trans.Reader
import CSlash.Driver.Pipeline.LogQueue
import qualified Data.Map.Strict as M
import CSlash.Types.TypeEnv
import Control.Monad.Trans.State.Lazy
import Control.Monad.Trans.Class
import CSlash.Driver.Env.KnotVars
import Control.Concurrent.STM
import Control.Monad.Trans.Maybe
-- import GHC.Runtime.Loader
import CSlash.Rename.Names
import CSlash.Utils.Constants
import CSlash.Types.Unique.DFM (udfmRestrictKeysSet)
import CSlash.Types.Unique
-- import CSlash.Iface.Errors.Types

import qualified CSlash.Data.Word64Set as W

import Debug.Trace (trace)
import CSlash.Tc.Errors.Types (TcRnMessage)

-- -----------------------------------------------------------------------------
-- Loading the program

depanalE :: CslMonad m => [ModuleName] -> Bool -> m (DriverMessages, ModuleGraph)
depanalE excluded_mods allow_dup_roots = do
  cs_env <- getSession
  (errs, mod_graph) <- depanalPartial excluded_mods allow_dup_roots
  if isEmptyMessages errs
    then do cs_env <- getSession
            let one_unit_messages get_mod_errs k hue = do
                  errs <- get_mod_errs
                  unknown_module_err <- warnUnknownModules (csSetActiveUnitId k cs_env)
                                                           (homeUnitEnv_dflags hue)
                                                           mod_graph
                  let unused_home_mod_err = warnMissingHomeModules (homeUnitEnv_dflags hue)
                                                                   (cs_targets cs_env)
                                                                   mod_graph
                      unused_pkg_err = warnUnusedPackages (homeUnitEnv_units hue)
                                                          (homeUnitEnv_dflags hue)
                                                          mod_graph
                  return $ errs `unionMessages` unused_home_mod_err
                                `unionMessages` unused_pkg_err
                                `unionMessages` unknown_module_err
            all_errs <- liftIO $ unitEnv_foldWithKey one_unit_messages
                                                     (return emptyMessages)
                                                     (cs_HUG cs_env)
            logDiagnostics (CsDriverMessage <$> all_errs)
            setSession cs_env { cs_mod_graph = mod_graph }
            pure (emptyMessages, mod_graph)
    else do setSession cs_env { cs_mod_graph = emptyMG }
            pure (errs, emptyMG)

depanalPartial :: CslMonad m => [ModuleName] -> Bool -> m (DriverMessages, ModuleGraph)
depanalPartial excluded_mods allow_dup_roots = do
  cs_env <- getSession
  let targets = cs_targets cs_env
      old_graph = cs_mod_graph cs_env
      logger = cs_logger cs_env

  withTiming logger (text "Chasing dependencies") (const ()) $ do
    liftIO $ debugTraceMsg logger 2 (hcat [ text "Chasing module from: "
                                          , hcat (punctuate comma (map pprTarget targets)) ])

    liftIO $ flushFinderCaches (cs_FC cs_env) (cs_unit_env cs_env)

    (errs, graph_nodes) <- liftIO $ downsweep
                           cs_env (mgModSummaries old_graph)
                           excluded_mods allow_dup_roots
    let mod_graph = mkModuleGraph graph_nodes
    return (unionManyMessages errs, mod_graph)

instantiationNodes :: UnitId -> UnitState -> [ModuleGraphNode]
instantiationNodes uid unit_state = InstantiationNode uid <$> iuids_to_check
  where
    iuids_to_check :: [InstantiatedUnit]
    iuids_to_check = nubSort $ concatMap (goUnitId . fst) (explicitUnits unit_state)
      where
        goUnitId uid = [ recur | VirtUnit indef <- [uid]
                               , inst <- instUnitInsts indef
                               , recur <- (indef :) $ goUnitId $ moduleUnit $ snd inst ]

linkNodes
  :: [ModuleGraphNode]
  -> UnitId
  -> HomeUnitEnv
  -> Maybe (Either (Messages DriverMessage) ModuleGraphNode)
linkNodes summaries uid hue =
  let dflags = homeUnitEnv_dflags hue
      ofile = outputFile_ dflags

      unit_nodes :: [NodeKey]
      unit_nodes = map mkNodeKey (filter ((== uid) . moduleGraphNodeUnitId) summaries)

      no_cs_main = gopt Opt_NoCsMain dflags

      main_sum =
        any (== NodeKey_Module (ModNodeKeyWithUid (mainModuleNameIs dflags) uid)) unit_nodes

      do_linking = main_sum || no_cs_main
                   || csLink dflags == LinkDynLib || csLink dflags == LinkStaticLib

  in if | csLink dflags == LinkBinary && isJust ofile && not do_linking
          -> Just (Left $ singleMessage $ mkPlainErrorMsgEnvelope noSrcSpan
                   (DriverRedirectedNoMain $ mainModuleNameIs dflags))
        | csLink dflags /= NoLink, do_linking -> Just (Right (LinkNode unit_nodes uid))
        | otherwise -> Nothing
            

warnMissingHomeModules :: DynFlags -> [Target] -> ModuleGraph -> DriverMessages
warnMissingHomeModules dflags targets mod_graph =
  if null missing then emptyMessages else warn
  where
    diag_opts = initDiagOpts dflags
    is_known_module mod = any (is_my_target mod) targets

    is_my_target mod target =
      let tuid = targetUnitId target
      in case targetId target of
           TargetModule name -> moduleName (ms_mod mod) == name
                                && tuid == ms_unitid mod
           TargetFile target_file _
             | Just mod_file <- ml_cs_file (ms_location mod)
               -> augmentByWorkingDirectory dflags target_file == mod_file
                  || mkModuleName (fst $ splitExtension target_file)
                     ==  moduleName (ms_mod mod)
           _ -> False

    missing = map (moduleName . ms_mod)
              $ filter (not . is_known_module)
              $ filter (\ms -> ms_unitid ms == homeUnitId_ dflags)
                       (mgModSummaries mod_graph)

    warn = singleMessage $ mkPlainMsgEnvelope diag_opts noSrcSpan
                         $ DriverMissingHomeModules (homeUnitId_ dflags) missing

warnUnknownModules :: CsEnv -> DynFlags -> ModuleGraph -> IO DriverMessages
warnUnknownModules cs_env dflags mod_graph = do
  reexported_warns <- filterM check_reexport (Set.toList reexported_mods)
  return $ final_msgs hidden_warns reexported_warns
  where
    diag_opts = initDiagOpts dflags
    unit_mods = Set.fromList (map ms_mod_name
                               (filter (\ms -> ms_unitid ms == homeUnitId_ dflags)
                                       (mgModSummaries mod_graph)))
    
    reexported_mods = reexportedModules dflags
    hidden_mods = hiddenModules dflags

    hidden_warns = hidden_mods `Set.difference` unit_mods

    lookupModule mn = findImportedModule cs_env mn NoPkgQual

    check_reexport mn = do
      fr <- lookupModule mn
      case fr of
        Found _ m -> return (moduleUnitId m == homeUnitId_ dflags)
        _ -> return True

    warn diagnostic = singleMessage $ mkPlainMsgEnvelope diag_opts noSrcSpan diagnostic

    final_msgs hidden_warns reexported_warns =
      unionManyMessages $
      [ warn (DriverUnknownHiddenModules (homeUnitId_ dflags) (Set.toList hidden_warns))
      | not (Set.null hidden_warns) ]
      ++ [ warn (DriverUnknownReexportedModules (homeUnitId_ dflags) reexported_warns)
         | not (null reexported_warns) ]

data LoadHowMuch
  = LoadAllTargets
  | LoadUpTo HomeUnitModule
  | LoadDependenciesOf HomeUnitModule

data ModIfaceCache = ModIfaceCache
  { iface_clearCache :: IO [CachedIface]
  , iface_addToCache :: CachedIface -> IO ()
  }

addHmiToCache :: ModIfaceCache -> HomeModInfo -> IO ()
addHmiToCache c (HomeModInfo i _ l) = iface_addToCache c (CachedIface i l)

data CachedIface = CachedIface
  { cached_modiface :: !ModIface
  , cached_linkable :: !HomeModLinkable
  }

instance Outputable CachedIface where
  ppr (CachedIface mi ln) = hsep [ text "CachedIface", ppr (miKey mi), ppr ln ]

noIfaceCache :: Maybe ModIfaceCache
noIfaceCache = Nothing

newIfaceCache :: IO ModIfaceCache
newIfaceCache = do
  ioref <- newIORef []
  return $
    ModIfaceCache
    { iface_clearCache = atomicModifyIORef' ioref (\c -> ([], c))
    , iface_addToCache = \hmi -> atomicModifyIORef' ioref (\c -> (hmi:c, ()))
    }

load :: CslMonad f => LoadHowMuch -> f SuccessFlag
load how_much = loadWithCache noIfaceCache mkUnknownDiagnostic how_much

mkBatchMsg :: CsEnv -> Messager
mkBatchMsg cs_env =
  if length (cs_all_home_unit_ids cs_env) > 1
  then batchMultiMsg
  else batchMsg

type AnyCslDiagnostic = UnknownDiagnostic (DiagnosticOpts CsMessage)

loadWithCache
  :: CslMonad m
  => Maybe ModIfaceCache
  -> (CsMessage -> AnyCslDiagnostic)
  -> LoadHowMuch
  -> m SuccessFlag
loadWithCache cache diag_wrapper how_much = do
  (errs, mod_graph) <- depanalE [] False
  msg <- mkBatchMsg <$> getSession
  success <- load' cache how_much diag_wrapper (Just msg) mod_graph
  if isEmptyMessages errs
    then pure success
    else throwErrors (fmap CsDriverMessage errs)

warnUnusedPackages :: UnitState -> DynFlags -> ModuleGraph -> DriverMessages
warnUnusedPackages us dflags mod_graph =
  let diag_opts = initDiagOpts dflags

      home_mod_sum = filter (\ms -> homeUnitId_ dflags == ms_unitid ms) (mgModSummaries mod_graph)

      loadedPackages = concat $
        mapMaybe (\(fs, mn) -> lookupModulePackage us (unLoc mn) fs)
        $ concatMap ms_imps home_mod_sum

      any_import_csl_prim = any ms_csl_prim_import home_mod_sum

      used_args = Set.fromList (map unitId loadedPackages)
                  `Set.union` Set.fromList [ primUnitId | any_import_csl_prim ]

      resolve (u, mflag) = do
        flag <- mflag
        ui <- lookupUnit us u
        guard (Set.notMember (unitId ui) used_args)
        return (unitId ui, unitPackageName ui, unitPackageVersion ui, flag)

      unusedArgs = sortOn (\(u, _, _, _) -> u) $ mapMaybe resolve (explicitUnits us)

      warn
        = singleMessage $ mkPlainMsgEnvelope diag_opts noSrcSpan (DriverUnusedPackages unusedArgs)

  in if null unusedArgs
     then emptyMessages
     else warn

data BuildPlan
  = SingleModule ModuleGraphNode
  | UnresolvedCycle [ModuleGraphNode]

instance Outputable BuildPlan where
  ppr (SingleModule mgn) = text "SingleModule" <> parens (ppr mgn)
  ppr (UnresolvedCycle mgn) = text "UnresolvedCycle:" <+> ppr mgn

countMods :: BuildPlan -> Int
countMods (SingleModule _) = 1
countMods (UnresolvedCycle ns) = length ns

createBuildPlan :: ModuleGraph -> Maybe HomeUnitModule -> [BuildPlan]
createBuildPlan mod_graph maybe_top_mod =
  let cycle_mod_graph = topSortModuleGraph mod_graph maybe_top_mod

      build_plan :: [BuildPlan]
      build_plan = collapseAcyclic cycle_mod_graph

      collapseAcyclic :: [SCC ModuleGraphNode] -> [BuildPlan]
      collapseAcyclic (AcyclicSCC node : nodes) = SingleModule node : collapseAcyclic nodes
      collapseAcyclic (CyclicSCC cy_nodes : nodes)
        = (UnresolvedCycle cy_nodes) : collapseAcyclic nodes
      collapseAcyclic [] = []
  in assertPpr (sum (map countMods build_plan) == length (mgModSummaries' mod_graph))
     (vcat [ text "Build plan missing nodes:"
           , text "PLAN:" <+> ppr (sum (map countMods build_plan))
           , text "GRAPH:" <+> ppr (length (mgModSummaries' mod_graph)) ])
     build_plan

data WorkerLimit
  = NumProcessorsLimit Int
  | JSemLimit SemaphoreName

mkWorkerLimit :: DynFlags -> IO WorkerLimit                                  
mkWorkerLimit dflags =
  case parMakeCount dflags of
    Nothing -> pure $ num_procs 1
    Just (ParMakeSemaphore h) -> pure (JSemLimit (SemaphoreName h))
    Just ParMakeNumProcessors -> num_procs <$> getNumProcessors
    Just (ParMakeThisMany n) -> pure $ num_procs n
  where
    num_procs x = NumProcessorsLimit (max 1 x)

isWorkerLimitSequential :: WorkerLimit -> Bool
isWorkerLimitSequential (NumProcessorsLimit x) = x <= 1
isWorkerLimitSequential (JSemLimit{}) = False

load'
  :: CslMonad m
  => Maybe ModIfaceCache
  -> LoadHowMuch
  -> (CsMessage -> AnyCslDiagnostic)
  -> Maybe Messager
  -> ModuleGraph
  -> m SuccessFlag
load' mhmi_cache how_much diag_wrapper mCsMessage mod_graph = do
  modifySession $ \cs_env -> cs_env { cs_mod_graph = mod_graph }
  guessOutputFile
  cs_env <- getSession

  let dflags = cs_dflags cs_env
      logger = cs_logger cs_env

      all_home_mods = Set.fromList [ Module (ms_unitid s) (ms_mod_name s)
                                   | s <- mgModSummaries mod_graph ]

      checkHowMuch (LoadUpTo m) = checkMod m
      checkHowMuch (LoadDependenciesOf m) = checkMod m
      checkHowMuch _ = id

      checkMod m and_then
        | m `Set.member` all_home_mods = and_then
        | otherwise = do
            liftIO $ errorMsg logger
              $ text "no such module:" <+>
              quotes (ppr (moduleUnit m) <> colon <> ppr (moduleName m))
            return Failed

  checkHowMuch how_much $ do
    let mg2 :: [SCC ModuleGraphNode]
        mg2 = topSortModuleGraph mod_graph Nothing

        maybe_top_mod = case how_much of
                          LoadUpTo m -> Just m
                          LoadDependenciesOf m -> Just m
                          _ -> Nothing

        build_plan = createBuildPlan mod_graph maybe_top_mod

    cache <- liftIO $ maybe (return []) iface_clearCache mhmi_cache

    let !pruned_cache = pruneCache cache (flattenSCCs (filterToposortToModules mg2))

        pruneHomeUnitEnv hme = hme { homeUnitEnv_hpt = emptyHomePackageTable }
    setSession $ csUpdateHUG (unitEnv_map pruneHomeUnitEnv) cs_env
    cs_env <- getSession

    liftIO $ debugTraceMsg logger 2 (hang (text "Reader for upsweep") 2 (ppr build_plan))

    worker_limit <- liftIO $ mkWorkerLimit dflags

    (upsweep_ok, new_deps) <- withDeferredDiagnostics $ do
      cs_env <- getSession
      liftIO $ upsweep worker_limit cs_env mhmi_cache diag_wrapper
                       mCsMessage (toCache pruned_cache) build_plan

    modifySession (addDepsToCsEnv new_deps)
    case upsweep_ok of
      Failed -> loadFinish upsweep_ok
      Succeeded -> do
        liftIO $ debugTraceMsg logger 2 (text "Upsweep completely successful.")
        loadFinish upsweep_ok

loadFinish :: CslMonad m => SuccessFlag -> m SuccessFlag
loadFinish all_ok = return all_ok

guessOutputFile :: CslMonad m => m ()
guessOutputFile = modifySession $ \env ->
  let !mod_graph = cs_mod_graph env
      new_home_graph =
        flip unitEnv_map (cs_HUG env) $ \hue ->
          let dflags = homeUnitEnv_dflags hue
              platform = targetPlatform dflags
              mainModuleSrcPath :: Maybe String
              mainModuleSrcPath = do
                ms <- mgLookupModule mod_graph (mainModIs hue)
                ml_cs_file (ms_location ms)
              name = fmap dropExtension mainModuleSrcPath
              name_prog = do
                !name' <- case platformArchOS platform of
                           _ -> name
                mainModuleSrcPath' <- mainModuleSrcPath
                if name' == mainModuleSrcPath'
                  then throwCsException . UsageError $
                       "default output name would overwrite the input file; " ++
                       "must specify -o explicitly"
                  else Just name'
          in case outputFile_ dflags of
               Just _ -> hue
               Nothing -> hue { homeUnitEnv_dflags = dflags { outputFile_ = name_prog } }
  in env { cs_unit_env = (cs_unit_env env) { ue_home_unit_graph = new_home_graph } }

-- -----------------------------------------------------------------------------
-- Prune the HomePackageTable

pruneCache :: [CachedIface] -> [ModSummary] -> [HomeModInfo]
pruneCache hpt summ = strictMap prune hpt
  where
    prune (CachedIface { cached_modiface = iface, cached_linkable = linkable })
      = HomeModInfo iface emptyModDetails linkable'
      where
        modl = miKey iface
        linkable'
          | Just ms <- M.lookup modl ms_map
          , mi_src_hash iface /= ms_cs_hash ms
          = emptyHomeModInfoLinkable
          | otherwise
          = linkable

    ms_map = M.fromListWith
             (\ms1 ms2 -> assertPpr False (text "prune_cache" $$ (ppr ms1 <+> ppr ms2)) ms2)
             [ (msKey ms, ms) | ms <- summ ]

data ResultVar b = forall a. ResultVar (a -> b) (MVar (Maybe a))

deriving instance Functor ResultVar

mkResultVar :: MVar (Maybe a) -> ResultVar a
mkResultVar = ResultVar id

waitResult :: ResultVar a -> MaybeT IO a
waitResult (ResultVar f var) = MaybeT (fmap f <$> readMVar var)

data BuildResult = BuildResult
  { _resultOrigin :: ResultOrigin
  , resultVar :: ResultVar (Maybe HomeModInfo, ModuleNameSet)
  }

data ResultOrigin = NoLoop | Loop ResultLoopOrigin deriving Show

data ResultLoopOrigin = Initialize | Finalized deriving Show

mkBuildResult :: ResultOrigin -> ResultVar (Maybe HomeModInfo, ModuleNameSet) -> BuildResult
mkBuildResult = BuildResult

data BuildLoopState = BuildLoopState
  { buildDep :: M.Map NodeKey BuildResult
  , nNODE :: Int
  , hug_var :: MVar HomeUnitGraph
  }

nodeId :: BuildM Int
nodeId = do
  n <- gets nNODE
  modify (\m -> m { nNODE = n + 1 })
  return n

setModulePipeline :: NodeKey -> BuildResult -> BuildM ()
setModulePipeline  mgn build_result =
  modify $ \m -> m { buildDep = M.insert mgn build_result (buildDep m) } 

type BuildMap = M.Map NodeKey BuildResult

getBuildMap :: BuildM BuildMap
getBuildMap = gets buildDep

getDependencies :: [NodeKey] -> BuildMap -> [BuildResult]
getDependencies direct_deps build_map =
  strictMap (expectJust "dep_map" . flip M.lookup build_map) direct_deps

type BuildM a = StateT BuildLoopState IO a

data MakeEnv = MakeEnv
  { cs_env :: !CsEnv
  , compile_sem :: !AbstractSem
  , withLogger :: forall a. Int -> ((Logger -> Logger) -> IO a) -> IO a
  , env_messager :: !(Maybe Messager)
  , diag_wrapper :: CsMessage -> AnyCslDiagnostic
  }

type RunMakeM a = ReaderT MakeEnv (MaybeT IO) a

interpretBuildPlan
  :: HomeUnitGraph
  -> Maybe ModIfaceCache
  -> M.Map ModNodeKeyWithUid HomeModInfo
  -> [BuildPlan]
  -> IO (Maybe [ModuleGraphNode], [MakeAction], IO [Maybe (Maybe HomeModInfo)])
interpretBuildPlan hug mhmi_cache old_hpt plan = do
  hug_var <- newMVar hug
  ((mcycle, plans), build_map) <- runStateT (buildLoop plan) (BuildLoopState M.empty 1 hug_var)
  let wait = collect_results (buildDep build_map)
  return (mcycle, plans, wait)

  where
    collect_results build_map = sequence (map (\br -> collect_result (fst <$> resultVar br))
                                              (M.elems build_map))
      where collect_result res_var = runMaybeT (waitResult res_var)

    n_mods = sum (map countMods plan)

    buildLoop :: [BuildPlan] -> BuildM (Maybe [ModuleGraphNode], [MakeAction])
    buildLoop [] = return (Nothing, [])
    buildLoop (plan:plans) =
      case plan of
        SingleModule m -> do
          one_plan <- buildSingleModule NoLoop m
          (cycle, all_plans) <- buildLoop plans
          return (cycle, one_plan : all_plans)
        UnresolvedCycle ns -> return (Just ns, [])

    buildSingleModule :: ResultOrigin -> ModuleGraphNode -> BuildM MakeAction
    buildSingleModule origin mod = do
      mod_idx <- nodeId
      !build_map <- getBuildMap
      hug_var <- gets hug_var
      let direct_deps = nodeDependencies mod
          !build_deps = getDependencies direct_deps build_map
          !build_action = case mod of
            InstantiationNode uid iu -> do
              withCurrentUnit (moduleGraphNodeUnitId mod) $ do
                (hug, deps) <- wait_deps_hug hug_var build_deps
                executeInstantiationNode mod_idx n_mods hug uid iu
                return (Nothing, deps)
            ModuleNode _ ms ->
              let !old_hmi = M.lookup (msKey ms) old_hpt
              in withCurrentUnit (moduleGraphNodeUnitId mod) $ do
                   (hug, deps) <- wait_deps_hug hug_var build_deps
                   hmi <- executeCompileNode mod_idx n_mods old_hmi hug ms
                   liftIO $ forM mhmi_cache $ \hmi_cache -> addHmiToCache hmi_cache hmi
                   liftIO $ modifyMVar_ hug_var (return . addHomeModInfoToHug hmi)
                   return ( Just hmi
                          , addToModuleNameSet (moduleGraphNodeUnitId mod) (ms_mod_name ms) deps )
            LinkNode _ uid -> do
              withCurrentUnit (moduleGraphNodeUnitId mod) $ do
                (hug, deps) <- wait_deps_hug hug_var build_deps
                executeLinkNode hug (mod_idx, n_mods) uid direct_deps
                return (Nothing, deps)
      
      res_var <- liftIO newEmptyMVar
      let result_var = mkResultVar res_var
      setModulePipeline (mkNodeKey mod) (mkBuildResult origin result_var)
      return $! (MakeAction build_action res_var)

withCurrentUnit :: UnitId -> RunMakeM a -> RunMakeM a
withCurrentUnit uid = local (\env -> env { cs_env = csSetActiveUnitId uid (cs_env env) })

upsweep
  :: WorkerLimit
  -> CsEnv
  -> Maybe ModIfaceCache
  -> (CsMessage -> AnyCslDiagnostic)
  -> Maybe Messager
  -> M.Map ModNodeKeyWithUid HomeModInfo
  -> [BuildPlan]
  -> IO (SuccessFlag, [HomeModInfo])
upsweep n_jobs cs_env hmi_cache diag_wrapper mCsMessage old_hpt build_plan = do
  (cycle, pipelines, collect_result) <-
    interpretBuildPlan (cs_HUG cs_env) hmi_cache old_hpt build_plan
  runPipelines n_jobs cs_env diag_wrapper mCsMessage pipelines
  res <- collect_result
  let completed = [ m | Just (Just m) <- res ]
  case cycle of
    Just mss -> do
      let logger = cs_logger cs_env
      liftIO $ fatalErrorMsg logger (cyclicModuleErr mss)
      return (Failed, [])
    Nothing -> do
      let success_flag = successIf (all isJust res)
      return (success_flag, completed)

toCache :: [HomeModInfo] -> M.Map (ModNodeKeyWithUid) HomeModInfo
toCache hmis = M.fromList [ (miKey $ hm_iface hmi, hmi) | hmi <- hmis ]

miKey :: ModIface -> ModNodeKeyWithUid
miKey hmi = ModNodeKeyWithUid (mi_mn hmi) (toUnitId $ moduleUnit (mi_module hmi))

upsweep_inst
  :: CsEnv
  -> Maybe Messager
  -> Int
  -> Int
  -> UnitId
  -> InstantiatedUnit
  -> IO ()
upsweep_inst cs_env mCsMessage mod_index nmods uid iuid = do
  case mCsMessage of
    Just csMessage -> csMessage cs_env
                                (mod_index, nmods)
                                (NeedsRecompile MustCompile)
                                (InstantiationNode uid iuid)
    Nothing -> return ()
  runCs cs_env $ ioMsgMaybe $ hoistTcRnMessage $ tcRnCheckUnit cs_env $ VirtUnit iuid
  pure ()

tcRnCheckUnit :: CsEnv -> Unit -> IO (Messages TcRnMessage, Maybe ())
tcRnCheckUnit cs_env uid = trace "tcRnCheckUnit"
  $ return (emptyMessages :: Messages TcRnMessage, Just ())

upsweep_mod
  :: CsEnv
  -> Maybe Messager
  -> Maybe HomeModInfo
  -> ModSummary
  -> Int
  -> Int
  -> IO HomeModInfo
upsweep_mod cs_env mCsMessage old_hmi summary mod_index nmods = 
  compileOne' mCsMessage cs_env summary mod_index nmods (hm_iface <$> old_hmi)
              (maybe emptyHomeModInfoLinkable hm_linkable old_hmi)

-- ---------------------------------------------------------------------------
-- Topological sort of the module graph

topSortModuleGraph :: ModuleGraph -> Maybe HomeUnitModule -> [SCC ModuleGraphNode]
topSortModuleGraph module_graph mb_root_mod =
  topSortModules (reverse $ mgModSummaries' module_graph) mb_root_mod

topSortModules :: [ModuleGraphNode] -> Maybe HomeUnitModule -> [SCC ModuleGraphNode]
topSortModules summaries mb_root_mod
  = map (fmap summaryNodeSummary) $ stronglyConnCompG initial_graph
  where
    (graph, lookup_node) = moduleGraphNodes summaries

    initial_graph = case mb_root_mod of
      Nothing -> graph
      Just (Module uid root_mod) ->
        let root | Just node <- lookup_node $ NodeKey_Module $ ModNodeKeyWithUid root_mod uid
                 , graph `hasVertexG` node
                 = node
                 | otherwise
                 = throwCsException (ProgramError "module does not exists")
        in graphFromEdgedVerticesUniq (seq root (reachableG graph root))

-----------------------------------------------------------------------------
-- Downsweep (dependency analysis)

type DownsweepCache = M.Map (UnitId, PkgQual, ModuleName) [Either DriverMessages ModSummary]

downsweep
  :: CsEnv -> [ModSummary] -> [ModuleName] -> Bool -> IO ([DriverMessages], [ModuleGraphNode])
downsweep cs_env old_summaries excl_mods allow_dup_roots = do
  (root_errs, rootSummariesOk) <- partitionWithM getRootSummary roots
  let root_map = mkRootMap rootSummariesOk
  checkDuplicates root_map
  (deps, map0) <- loopSummaries rootSummariesOk (M.empty, root_map)
  let closure_errs = checkHomeUnitsClosed (cs_unit_env cs_env)
      unit_env = cs_unit_env cs_env
      tmpfs = cs_tmpfs cs_env

      downsweep_errs = lefts $ concat $ M.elems map0
      downsweep_nodes = M.elems deps

      (other_errs, unit_nodes) = partitionEithers $ unitEnv_foldWithKey
        (\nodes uid hue -> nodes ++ unitModuleNodes downsweep_nodes uid hue) [] (cs_HUG cs_env)
      all_nodes = downsweep_nodes ++ unit_nodes
      all_errs = all_root_errs ++ downsweep_errs ++ other_errs
      all_root_errs = closure_errs ++ map snd root_errs

  if null all_root_errs
    then return (all_errs, all_nodes)
    else return (all_root_errs, [])
  where
    unitModuleNodes
      :: [ModuleGraphNode]
      -> UnitId
      -> HomeUnitEnv
      -> [Either (Messages DriverMessage) ModuleGraphNode]
    unitModuleNodes summaries uid hue =
      let instantiation_nodes = instantiationNodes uid (homeUnitEnv_units hue)
      in map Right instantiation_nodes
         ++ maybeToList (linkNodes (instantiation_nodes ++ summaries) uid hue)

    calcDeps ms = [ (ms_unitid ms, b, c) | (b, c) <- msDeps ms ]

    logger = cs_logger cs_env
    roots = cs_targets cs_env

    old_summary_map :: M.Map (UnitId, FilePath) ModSummary
    old_summary_map = M.fromList [((ms_unitid ms, msCsFilePath ms), ms) | ms <- old_summaries]

    getRootSummary :: Target -> IO (Either (UnitId, DriverMessages) ModSummary)
    getRootSummary Target { targetId = TargetFile file mb_phase
                          , targetContents = maybe_buf
                          , targetUnitId = uid } = do
      let dflags = homeUnitEnv_dflags (ue_findHomeUnitEnv uid (cs_unit_env cs_env))
          home_unit = ue_unitHomeUnit uid (cs_unit_env cs_env)
          offset_file = augmentByWorkingDirectory dflags file
      exists <- liftIO $ doesFileExist offset_file
      if exists || isJust maybe_buf
        then first (uid, ) <$>
             summarizeFile cs_env home_unit old_summary_map offset_file mb_phase maybe_buf
        else return $ Left $ (uid, ) $ singleMessage
             $ mkPlainErrorMsgEnvelope noSrcSpan (DriverFileNotFound offset_file)
    getRootSummary Target { targetId = TargetModule modl
                          , targetContents = maybe_buf
                          , targetUnitId = uid } = do
      let home_unit = ue_unitHomeUnit uid (cs_unit_env cs_env)
      maybe_summary <- summarizeModule cs_env home_unit old_summary_map
                                       (L rootLoc modl) (ThisPkg (homeUnitId home_unit))
                                       maybe_buf excl_mods
      case maybe_summary of
        FoundHome s -> return $ Right s
        FoundHomeWithError err -> return $ Left err
        _ -> return $ Left (uid, moduleNotFoundErr modl)

    rootLoc = mkGeneralSrcSpan (fsLit "<command line>")

    checkDuplicates :: DownsweepCache -> IO ()
    checkDuplicates root_map
      | allow_dup_roots = return ()
      | null dup_roots = return ()
      | otherwise = liftIO $ multiRootsErr (head dup_roots)
      where
        dup_roots :: [[ModSummary]]
        dup_roots = filterOut isSingleton $ map rights (M.elems root_map)

    loopSummaries
      :: [ModSummary]
      -> (M.Map NodeKey ModuleGraphNode, DownsweepCache)
      -> IO ((M.Map NodeKey ModuleGraphNode), DownsweepCache)    
    loopSummaries [] done = return done
    loopSummaries (ms : next) (done, summarized)
      | Just {} <- M.lookup k done
      = loopSummaries next (done, summarized)
      | otherwise = do
          (final_deps, done', summarized') <- loopImports (calcDeps ms) done summarized
          loopSummaries next (M.insert k (ModuleNode final_deps ms) done', summarized')
      where
        k = NodeKey_Module (msKey ms)

    loopImports
      :: [(UnitId, PkgQual, Located ModuleName)]
      -> M.Map NodeKey ModuleGraphNode
      -> DownsweepCache
      -> IO ([NodeKey], M.Map NodeKey ModuleGraphNode, DownsweepCache)
    loopImports [] done summarized = return ([], done, summarized)
    loopImports ((home_uid, mb_pkg, wanted_mod) : ss) done summarized
      | Just summs <- M.lookup cache_key summarized
      = case summs of
          [Right ms] -> do
            let nk = NodeKey_Module (msKey ms)
            (rest, summarized', done') <- loopImports ss done summarized
            return (nk : rest, summarized', done')
          [Left _] -> loopImports ss done summarized
          _ -> loopImports ss done summarized
      | otherwise
      = do
          mb_s <-
            summarizeModule cs_env home_unit old_summary_map wanted_mod mb_pkg Nothing excl_mods
          case mb_s of
            NotThere -> loopImports ss done summarized
            External _ -> loopImports ss done summarized
            FoundInstantiation iud -> do
              (other_deps, done', summarized') <- loopImports ss done summarized
              return (NodeKey_Unit iud : other_deps, done', summarized')
            FoundHomeWithError (_, e) ->
              loopImports ss done (Map.insert cache_key [Left e] summarized)
            FoundHome s -> do
              (done', summarized') <-
                loopSummaries [s] (done, Map.insert cache_key [Right s] summarized)
              (other_deps, final_done, final_summarized) <- loopImports ss done' summarized'
              return (NodeKey_Module (msKey s) : other_deps, final_done, final_summarized)
      where
        L loc mod = wanted_mod
        cache_key = (home_uid, mb_pkg, mod)
        home_unit = ue_unitHomeUnit home_uid (cs_unit_env cs_env)

checkHomeUnitsClosed :: UnitEnv -> [DriverMessages]
checkHomeUnitsClosed ue
  | Set.null bad_unit_ids = []
  | otherwise = [singleMessage $ mkPlainErrorMsgEnvelope rootLoc
                 $ DriverHomePackagesNotClosed (Set.toList bad_unit_ids)]
  where
    home_id_set = unitEnv_keys $ ue_home_unit_graph ue
    bad_unit_ids = upwards_closure Set.\\ home_id_set
    rootLoc = mkGeneralSrcSpan (fsLit "<command line>")

    graph :: Graph (Node UnitId UnitId)
    graph = graphFromEdgedVerticesUniq graphNodes

    downwards_closure
      = graphFromEdgedVerticesUniq [ DigraphNode uid uid (Set.toList deps)
                                   | (uid, deps) <- M.toList (allReachable graph node_key) ]

    inverse_closure = transposeG downwards_closure

    upwards_closure = Set.fromList $ map node_key $ reachablesG inverse_closure
                      [DigraphNode uid uid [] | uid <- Set.toList home_id_set ]

    all_unit_direct_deps :: UniqMap UnitId (Set.Set UnitId)
    all_unit_direct_deps = unitEnv_foldWithKey go emptyUniqMap $ ue_home_unit_graph ue
      where
        go rest this this_uis =
          plusUniqMap_C Set.union
          (addToUniqMap_C Set.union external_depends this (Set.fromList $ this_deps)) rest
          where
            external_depends = mapUniqMap (Set.fromList . unitDepends) (unitInfoMap this_units)
            this_units = homeUnitEnv_units this_uis
            this_deps = [ toUnitId unit | (unit, Just _) <- explicitUnits this_units ]

    graphNodes :: [Node UnitId UnitId]
    graphNodes = go Set.empty home_id_set
      where
        go done todo = case Set.minView todo of
                         Nothing -> []
                         Just (uid, todo')
                           | Set.member uid done -> go done todo'
                           | otherwise -> case lookupUniqMap all_unit_direct_deps uid of
                                            Nothing -> pprPanic "uid not found"
                                                       (ppr (uid, all_unit_direct_deps))
                                            Just depends ->
                                              let todo'' = (depends Set.\\ done) `Set.union` todo'
                                              in DigraphNode uid uid (Set.toList depends)
                                                 : go (Set.insert uid done) todo''

mkRootMap :: [ModSummary] -> DownsweepCache
mkRootMap summaries = Map.fromListWith (flip (++))
  [ ((ms_unitid s, NoPkgQual, ms_mod_name s), [Right s]) | s <- summaries ]

-----------------------------------------------------------------------------
-- Summarising modules

data SummarizeResult
  = FoundInstantiation InstantiatedUnit
  | FoundHomeWithError (UnitId, DriverMessages)
  | FoundHome ModSummary
  | External UnitId
  | NotThere

summarizeFile
  :: CsEnv
  -> HomeUnit
  -> M.Map (UnitId, FilePath) ModSummary
  -> FilePath
  -> Maybe Phase
  -> Maybe (StringBuffer, UTCTime)
  -> IO (Either DriverMessages ModSummary)
summarizeFile cs_env' home_unit old_summaries src_fn mb_phase maybe_buf
  | Just old_summary <- M.lookup (homeUnitId home_unit, src_fn) old_summaries
  = do let location = ms_location old_summary
       src_hash <- get_src_hash
       checkSummaryHash cs_env (new_summary src_fn) old_summary location src_hash
  | otherwise
  = do src_hash <- get_src_hash
       new_summary src_fn src_hash
  where
    cs_env = csSetActiveHomeUnit home_unit cs_env'
    get_src_hash = case maybe_buf of
                     Just (buf, _) -> return $ fingerprintStringBuffer buf
                     Nothing -> liftIO $ getFileHash src_fn

    new_summary src_fn src_hash = runExceptT $ do
      preimps@PreprocessedImports{..} <- getPreprocessedImports cs_env src_fn mb_phase maybe_buf
      let fopts = initFinderOpts (cs_dflags cs_env)
          location = mkHomeModLocation fopts pi_mod_name src_fn
      mod <- liftIO $
        let home_unit = cs_home_unit cs_env
            fc = cs_FC cs_env
        in addHomeModuleToFinder fc home_unit pi_mod_name location
      liftIO $ makeNewModSummary cs_env $ MakeNewModSummary
        { nms_src_fn = src_fn
        , nms_src_hash = src_hash
        , nms_cs_src = CsSrcFile
        , nms_location = location
        , nms_mod = mod
        , nms_preimps = preimps
        }

checkSummaryHash
  :: CsEnv
  -> (Fingerprint -> IO (Either e ModSummary))
  -> ModSummary
  -> ModLocation
  -> Fingerprint
  -> IO (Either e ModSummary)
checkSummaryHash cs_env new_summary old_summary location src_hash
  | ms_cs_hash old_summary == src_hash
    && not (gopt Opt_ForceRecomp (cs_dflags cs_env)) = do
      obj_timestamp <- modificationTimeIfExists (ml_obj_file location)
      _ <- let fc = cs_FC cs_env
           in case ms_cs_src old_summary of
                CsSrcFile -> addModuleToFinder fc (ms_mod old_summary) location
                _ -> return ()
      hi_timestamp <- modificationTimeIfExists (ml_hi_file location)
      hie_timestamp <- modificationTimeIfExists (ml_hie_file location)

      return $ Right $ old_summary { ms_obj_date = obj_timestamp
                                   , ms_iface_date = hi_timestamp
                                   , ms_hie_date = hie_timestamp
                                   }
  | otherwise
  = new_summary src_hash

summarizeModule
  :: CsEnv
  -> HomeUnit
  -> M.Map (UnitId, FilePath) ModSummary
  -> Located ModuleName
  -> PkgQual
  -> Maybe (StringBuffer, UTCTime)
  -> [ModuleName]
  -> IO SummarizeResult
summarizeModule cs_env' home_unit old_summary_map (L _ wanted_mod) mb_pkg maybe_buf excl_mods
  | wanted_mod `elem` excl_mods
  = return NotThere
  | otherwise
  = find_it
  where
    cs_env = csSetActiveHomeUnit home_unit cs_env'
    dflags = cs_dflags cs_env

    find_it :: IO SummarizeResult
    find_it = do
      found <- findImportedModule cs_env wanted_mod mb_pkg
      case found of
        Found location mod
          | isJust (ml_cs_file location) -> just_found location mod
          | VirtUnit iud <- moduleUnit mod
          , not (isHomeModule home_unit mod)
            -> return $ FoundInstantiation iud
          | otherwise -> return $ External $ moduleUnitId mod
        _ -> return NotThere

    just_found location mod = do
      let src_fn = expectJust "summarize2" (ml_cs_file location)
      maybe_h <- fileHashIfExists src_fn
      case maybe_h of
        Nothing -> return NotThere
        Just h -> do
          fresult <- new_summary_cache_check location mod src_fn h
          return $ case fresult of
            Left err -> FoundHomeWithError (moduleUnitId mod, err)
            Right ms -> FoundHome ms

    new_summary_cache_check loc mod src_fn h
      | Just old_summary <- Map.lookup (toUnitId (moduleUnit mod), src_fn) old_summary_map
      = case maybe_buf of
          Just (buf, _) -> checkSummaryHash
            cs_env (new_summary loc mod src_fn) old_summary loc (fingerprintStringBuffer buf)
          Nothing -> checkSummaryHash
            cs_env (new_summary loc mod src_fn) old_summary loc h
      | otherwise = new_summary loc mod src_fn h

    new_summary
      :: ModLocation
      -> Module
      -> FilePath
      -> Fingerprint
      -> IO (Either DriverMessages ModSummary)
    new_summary location mod src_fn src_hash = runExceptT $ do
      preimps@PreprocessedImports{..} <-
        getPreprocessedImports
        (csSetActiveUnitId (moduleUnitId mod) cs_env) src_fn Nothing maybe_buf
      let cs_src = CsSrcFile
      when (pi_mod_name /= wanted_mod) $
        throwE $ singleMessage $ mkPlainErrorMsgEnvelope pi_mod_name_loc
               $ DriverFileModuleNameMismatch pi_mod_name wanted_mod

      liftIO $ makeNewModSummary cs_env $ MakeNewModSummary
        { nms_src_fn = src_fn
        , nms_src_hash = src_hash
        , nms_cs_src = cs_src
        , nms_location = location
        , nms_mod = mod
        , nms_preimps = preimps
        }

data MakeNewModSummary = MakeNewModSummary
  { nms_src_fn :: FilePath
  , nms_src_hash :: Fingerprint
  , nms_cs_src :: CsSource
  , nms_location :: ModLocation
  , nms_mod :: Module
  , nms_preimps :: PreprocessedImports
  }

makeNewModSummary :: CsEnv -> MakeNewModSummary -> IO ModSummary
makeNewModSummary cs_env MakeNewModSummary{..} = do
  let PreprocessedImports{..} = nms_preimps
  obj_timestamp <- modificationTimeIfExists (ml_obj_file nms_location)
  dyn_obj_timestamp <- modificationTimeIfExists (ml_dyn_obj_file nms_location)
  hi_timestamp <- modificationTimeIfExists (ml_hi_file nms_location)
  hie_timestamp <- modificationTimeIfExists (ml_hie_file nms_location)

  (implicit_sigs, _) <-
    implicitRequirementsShallow (csSetActiveUnitId (moduleUnitId nms_mod) cs_env) pi_theimps

  return $ ModSummary
    { ms_mod = nms_mod
    , ms_cs_src = nms_cs_src
    , ms_location = nms_location
    , ms_cs_file = pi_cs_fn
    , ms_cs_opts = pi_local_dflags
    , ms_cs_buf = Just pi_cs_buf
    , ms_parsed_mod = Nothing
    , ms_csl_prim_import = pi_csl_prim_import
    , ms_textual_imps = ((,) NoPkgQual . noLoc <$> implicit_sigs) ++ pi_theimps
    , ms_cs_hash = nms_src_hash
    , ms_iface_date = hi_timestamp
    , ms_hie_date = hie_timestamp
    , ms_obj_date = obj_timestamp
    , ms_dyn_obj_date = dyn_obj_timestamp
    }

implicitRequirementsShallow
  :: CsEnv -> [(PkgQual, Located ModuleName)] -> IO ([ModuleName], [InstantiatedUnit])
implicitRequirementsShallow cs_env normal_imports =
  trace "calling implicitRequirementsShallow" $ go ([], []) normal_imports
  where
    mhome_unit = cs_home_unit_maybe cs_env

    go acc [] = pure acc
    go (accL, accR) ((mb_pkg, L _ imp) : imports) = do
      found <- findImportedModule cs_env imp mb_pkg
      let acc' = case found of
                   Found _ mod | notHomeModuleMaybe mhome_unit mod
                                 -> case moduleUnit mod of
                                      HoleUnit -> trace "iRS found HoleUnit"
                                                  (moduleName mod : accL, accR)
                                      RealUnit _ -> (accL, accR)
                                      VirtUnit u -> trace "iRS found VirtUnit"
                                                    (accL, u : accR)
                   _ -> (accL, accR)
      go acc' imports

data PreprocessedImports = PreprocessedImports
  { pi_local_dflags :: DynFlags
  , pi_theimps :: [(PkgQual, Located ModuleName)]
  , pi_csl_prim_import :: Bool
  , pi_cs_fn :: FilePath
  , pi_cs_buf :: StringBuffer
  , pi_mod_name_loc :: SrcSpan
  , pi_mod_name :: ModuleName
  }

getPreprocessedImports
  :: CsEnv
  -> FilePath
  -> Maybe Phase
  -> Maybe (StringBuffer, UTCTime)
  -> ExceptT DriverMessages IO PreprocessedImports
getPreprocessedImports cs_env src_fn mb_phase maybe_buf = do
  (pi_local_dflags, pi_cs_fn) <- ExceptT $ preprocess cs_env src_fn (fst <$> maybe_buf) mb_phase
  pi_cs_buf <- liftIO $ hGetStringBuffer pi_cs_fn
  (pi_theimps', pi_csl_prim_import, L pi_mod_name_loc pi_mod_name) <-
    ExceptT $ do
    let popts = initParserOpts pi_local_dflags
    mimps <- getImports popts pi_cs_buf pi_cs_fn src_fn
    return (first (mkMessages . fmap mkDriverPsHeaderMessage . getMessages) mimps)
  let rn_pkg_qual = renameRawPkgQual (cs_unit_env cs_env)
      rn_imps = fmap (\(pk, lmn@(L _ mn)) -> (rn_pkg_qual mn pk, lmn))
      pi_theimps = rn_imps pi_theimps'
  return PreprocessedImports{..}

-----------------------------------------------------------------------------
--                      Error messages
-----------------------------------------------------------------------------

withDeferredDiagnostics :: CslMonad m => m a -> m a
withDeferredDiagnostics f = do
  dflags <- getDynFlags
  if not $ gopt Opt_DeferDiagnostics dflags
    then f
    else do warnings <- liftIO $ newIORef []
            errors <- liftIO $ newIORef []
            fatals <- liftIO $ newIORef []
            logger <- getLogger

            let deferDiagnostics _ !msgClass !srcSpan !msg = 
                  let action = logMsg logger msgClass srcSpan msg
                  in case msgClass of
                       MCDiagnostic SevWarning _ _
                         -> atomicModifyIORef' warnings $ \(!i) -> (action : i, ())
                       MCDiagnostic SevError _ _
                         -> atomicModifyIORef' errors $ \(!i) -> (action : i, ())
                       MCFatal
                         -> atomicModifyIORef' fatals $ \(!i) -> (action : i, ())
                       _ -> action
                printDeferredDiagnostics = liftIO
                  $ forM_ [warnings, errors, fatals] $ \ref -> do
                  let landmine = if debugIsOn
                                 then panic "withDeferredDiagnostics: use after free"
                                 else []
                  actions <- atomicModifyIORef ref $ \i -> (landmine, i)
                  sequence_ $ reverse actions

            MC.bracket
              (pushLogHookM (const deferDiagnostics))
              (\_ -> popLogHookM >> printDeferredDiagnostics)
              (\_ -> f)

moduleNotFoundErr :: ModuleName -> DriverMessages
moduleNotFoundErr mod
  = singleMessage $ mkPlainErrorMsgEnvelope noSrcSpan (DriverModuleNotFound mod)

multiRootsErr :: [ModSummary] -> IO ()
multiRootsErr [] = panic "multiRootsErr"
multiRootsErr summs@(summ1:_)
  = throwOneError $ fmap CsDriverMessage
    $ mkPlainErrorMsgEnvelope noSrcSpan $ DriverDuplicatedModuleDeclaration mod files
  where
    mod = ms_mod summ1
    files = map (expectJust "checkDup" . ml_cs_file . ms_location) summs

cyclicModuleErr :: [ModuleGraphNode] -> SDoc
cyclicModuleErr mss =
  assert (not (null mss)) $
  case findCycle graph of
    Nothing -> text "Unexpected non-cycle" <+> ppr mss
    Just path0 -> vcat [ text "Module graph contains a cycle:"
                       , nest 2 (show_path path0)]
  where
    graph :: [Node NodeKey ModuleGraphNode]
    graph = [ DigraphNode { node_payload = ms
                          , node_key = mkNodeKey ms
                          , node_dependencies = nodeDependencies ms
                          }
            | ms <- mss ]

    show_path :: [ModuleGraphNode] -> SDoc
    show_path [] = panic "show_path"
    show_path [m] = ppr_node m <+> text "imports itself"
    show_path (m1:m2:ms) = vcat ( nest 14 (ppr_node m1)
                                : nest 6 (text "imports" <+> ppr_node m2)
                                : go ms )
      where
        go [] = [ text "which imports" <+> ppr_node m1 ]
        go (m:ms) = (text "which imports" <+> ppr_node m) : go ms

    ppr_node :: ModuleGraphNode -> SDoc
    ppr_node (ModuleNode _ m) = text "module" <+> ppr_ms m
    ppr_node (InstantiationNode _ u) = text "instantiated unit" <+> ppr u
    ppr_node (LinkNode uid _) = pprPanic "LinkNode should not be in a cycle" (ppr uid)

    ppr_ms :: ModSummary -> SDoc
    ppr_ms ms = quotes (ppr (moduleName (ms_mod ms)))
                <+> (parens (text (msCsFilePath ms)))

cleanCurrentModuleTempFilesMaybe :: MonadIO m => Logger -> TmpFs -> DynFlags -> m ()
cleanCurrentModuleTempFilesMaybe logger tmpfs dflags =
  if gopt Opt_KeepTmpFiles dflags
  then liftIO $ keepCurrentModuleTempFiles logger tmpfs
  else liftIO $ cleanCurrentModuleTempFiles logger tmpfs

addDepsToCsEnv :: [HomeModInfo] -> CsEnv -> CsEnv
addDepsToCsEnv deps cs_env =
  csUpdateHUG (\hug -> foldr addHomeModInfoToHug hug deps) cs_env

setHUG :: HomeUnitGraph -> CsEnv -> CsEnv
setHUG deps cs_env = csUpdateHUG (const deps) cs_env

wrapAction :: (CsMessage -> AnyCslDiagnostic) -> CsEnv -> IO a -> IO (Maybe a)
wrapAction msg_wrapper cs_env k = do
  let lcl_logger = cs_logger cs_env
      lcl_dynflags = cs_dflags cs_env
      print_config = initPrintConfig lcl_dynflags
      logg err = printMessages lcl_logger print_config (initDiagOpts lcl_dynflags)
                               (msg_wrapper <$> srcErrorMessages err)
  mres <- MC.try $ liftIO $ prettyPrintCsErrors lcl_logger k
  case mres of
    Right res -> return $ Just res
    Left exc -> do
      case fromException exc of
        Just (err :: SourceError) -> logg err
        Nothing -> case fromException exc of
                     Just (err :: SomeAsyncException) -> throwIO err
                     _ -> errorMsg lcl_logger (text (show exc))
      return Nothing

withParLog :: TVar LogQueueQueue -> Int -> ((Logger -> Logger) -> IO a) -> IO a
withParLog lqq_var k cont = 
  let init_log = do
        lq <- newLogQueue k
        atomically $ initLogQueue lqq_var lq
        return lq
      finish_log lq = liftIO (finishLogQueue lq)
  in MC.bracket init_log finish_log $ \lq -> cont (pushLogHook (const (parLogAction lq)))

withLoggerCs :: Int -> MakeEnv -> (CsEnv -> IO a) -> IO a
withLoggerCs k MakeEnv { withLogger, cs_env } cont = do
  withLogger k $ \modifyLogger ->
    let lcl_logger = modifyLogger (cs_logger cs_env)
        cs_env' = cs_env { cs_logger = lcl_logger }
    in cont cs_env'

executeInstantiationNode
  :: Int -> Int -> HomeUnitGraph -> UnitId -> InstantiatedUnit -> RunMakeM ()
executeInstantiationNode k n deps uid iu = do
  env <- ask
  msg <- asks env_messager
  wrapper <- asks diag_wrapper
  lift $ MaybeT $ withLoggerCs k env $ \cs_env ->
    let lcl_cs_env = setHUG deps cs_env
    in wrapAction wrapper lcl_cs_env $ do
         res <- upsweep_inst lcl_cs_env msg k n uid iu
         cleanCurrentModuleTempFilesMaybe (cs_logger cs_env) (cs_tmpfs cs_env) (cs_dflags cs_env)
         return res

executeCompileNode
  :: Int
  -> Int
  -> Maybe HomeModInfo
  -> HomeUnitGraph
  -> ModSummary
  -> RunMakeM HomeModInfo
executeCompileNode k n !old_hmi hug mod = do
  me@MakeEnv{..} <- ask
  lift $ MaybeT $ withAbstractSem compile_sem $ withLoggerCs k me $ \cs_env -> do
    let lcl_dynflags = ms_cs_opts mod
        lcl_cs_env = csSetFlags lcl_dynflags cs_env
    wrapAction diag_wrapper lcl_cs_env $ do
      res <- upsweep_mod lcl_cs_env env_messager old_hmi mod k n
      cleanCurrentModuleTempFilesMaybe (cs_logger cs_env) (cs_tmpfs cs_env) lcl_dynflags
      return res

executeLinkNode :: HomeUnitGraph -> (Int, Int) -> UnitId -> [NodeKey] -> RunMakeM ()
executeLinkNode hug kn uid deps =
  withCurrentUnit uid $ do
  MakeEnv{..} <- ask
  let dflags = cs_dflags cs_env
      cs_env' = setHUG hug cs_env
      msg' = (\messager recomp -> messager cs_env kn recomp (LinkNode deps uid)) <$> env_messager
  linkresult <- liftIO $ withAbstractSem compile_sem $ do
    link (csLink dflags)
         (cs_logger cs_env')
         (cs_tmpfs cs_env')
         (cs_FC cs_env')
         dflags
         (cs_unit_env cs_env')
         True
         msg'
         (cs_HPT cs_env')
  case linkresult of
    Failed -> fail "Link Failed"
    Succeeded -> return ()

type ModuleNameSet = M.Map UnitId W.Word64Set

addToModuleNameSet :: UnitId -> ModuleName -> ModuleNameSet -> ModuleNameSet
addToModuleNameSet uid mn s =
  let k = getKey $ getUnique mn
  in M.insertWith (W.union) uid (W.singleton k) s

wait_deps_hug
  :: MVar HomeUnitGraph
  -> [BuildResult]
  -> ReaderT MakeEnv (MaybeT IO) (HomeUnitGraph, ModuleNameSet)
wait_deps_hug hug_var deps = do
  (_, module_deps) <- wait_deps deps
  hug <- liftIO $ readMVar hug_var
  let pruneHomeUnitEnv uid hme =
        let !new = udfmRestrictKeysSet (homeUnitEnv_hpt hme)
                                       (fromMaybe W.empty $ M.lookup uid module_deps)
        in hme { homeUnitEnv_hpt = new }
  return (unitEnv_mapWithKey pruneHomeUnitEnv hug, module_deps)

wait_deps :: [BuildResult] -> RunMakeM ([HomeModInfo], ModuleNameSet)
wait_deps [] = return ([], M.empty)
wait_deps (x:xs) = do
  (res, deps) <- lift $ waitResult (resultVar x)
  (hmis, all_deps) <- wait_deps xs
  let !new_deps = deps `unionModuleNameSet` all_deps
  case res of
    Nothing -> return (hmis, new_deps)
    Just hmi -> return (hmi:hmis, new_deps)
  where
    unionModuleNameSet = M.unionWith W.union

-- Executing the pipelines

label_self :: String -> IO ()
label_self thread_name = do
    self_tid <- CC.myThreadId
    CC.labelThread self_tid thread_name

runPipelines
  :: WorkerLimit
  -> CsEnv
  -> (CsMessage -> AnyCslDiagnostic)
  -> Maybe Messager
  -> [MakeAction]
  -> IO ()
runPipelines n_job cs_env diag_wrapper mCsMessager all_pipelines = do
  liftIO $ label_self "main --make thread"
  case n_job of
    NumProcessorsLimit n | n <= 1 -> runSeqPipelines cs_env diag_wrapper mCsMessager all_pipelines
    _ -> runParPipelines n_job cs_env diag_wrapper mCsMessager all_pipelines

runSeqPipelines
  :: CsEnv -> (CsMessage -> AnyCslDiagnostic) -> Maybe Messager -> [MakeAction] -> IO ()
runSeqPipelines cs_env diag_wrapper mCsMessager all_pipelines =
  let env = MakeEnv { cs_env = cs_env
                    , withLogger = \_ k -> k id
                    , compile_sem = AbstractSem (return ()) (return ())
                    , env_messager = mCsMessager
                    , diag_wrapper = diag_wrapper
                    }
  in runAllPipelines (NumProcessorsLimit 1) env all_pipelines

runParPipelines
  :: WorkerLimit
  -> CsEnv
  -> (CsMessage -> AnyCslDiagnostic)
  -> Maybe Messager
  -> [MakeAction]
  -> IO ()
runParPipelines worker_limit cs_env diag_wrapper mCsMessager all_pipelines = do
  stopped_var <- newTVarIO False
  log_queue_queue_var <- newTVarIO newLogQueueQueue
  wait_log_thread <- logThread (cs_logger cs_env) stopped_var log_queue_queue_var

  thread_safe_logger <- liftIO $ makeThreadSafe (cs_logger cs_env)
  let thread_safe_cs_env = cs_env { cs_logger = thread_safe_logger }

  runWorkerLimit worker_limit $ \abstract_sem -> do
    let env = MakeEnv { cs_env = thread_safe_cs_env
                      , withLogger = withParLog log_queue_queue_var
                      , compile_sem = abstract_sem
                      , env_messager = mCsMessager
                      , diag_wrapper = diag_wrapper
                      }
    runAllPipelines worker_limit env all_pipelines
    atomically $ writeTVar stopped_var True
    wait_log_thread

runWorkerLimit :: WorkerLimit -> (AbstractSem -> IO a) -> IO a
runWorkerLimit worker_limit action = case worker_limit of
  NumProcessorsLimit n_jobs ->
    runNjobsAbstractSem n_jobs action
  JSemLimit sem ->
    runJSemAbstractSem sem action

runNjobsAbstractSem :: Int -> (AbstractSem -> IO a) -> IO a
runNjobsAbstractSem n_jobs action = do
  compile_sem <- newQSem n_jobs
  n_capabilities <- getNumCapabilities
  n_cpus <- getNumProcessors
  let asem = AbstractSem (waitQSem compile_sem) (signalQSem compile_sem)
      set_num_caps n = unless (n_capabilities /= 1) $ setNumCapabilities n
      updNumCapabilities = set_num_caps $ min n_jobs n_cpus
      resetNumCapabilities = set_num_caps n_capabilities
  MC.bracket_ updNumCapabilities resetNumCapabilities $ action asem

runAllPipelines :: WorkerLimit -> MakeEnv -> [MakeAction] -> IO ()
runAllPipelines worker_limit env acts = 
  let single_worker = isWorkerLimitSequential worker_limit
      spawn_actions :: IO [ThreadId]
      spawn_actions = if single_worker
        then (:[]) <$> (forkIOWithUnmask $ \unmask -> void $ runLoop (\io -> io unmask) env acts)
        else runLoop forkIOWithUnmask env acts

      kill_actions :: [ThreadId] -> IO ()
      kill_actions tids = mapM_ killThread tids
  in MC.bracket spawn_actions kill_actions $ \_ -> mapM_ waitMakeAction acts

runLoop :: (((forall a. IO a -> IO a) -> IO ()) -> IO a) -> MakeEnv -> [MakeAction] -> IO [a]
runLoop _ _ [] = return []
runLoop fork_thread env (MakeAction act res_var : acts) = do
  new_thread <- fork_thread $ \unmask -> do mres <- (unmask $ run_pipeline (withLocalTmpFS act))
                                                    `MC.onException` (putMVar res_var Nothing)
                                            putMVar res_var mres
  threads <- runLoop fork_thread env acts
  return (new_thread : threads)
  where
    run_pipeline :: RunMakeM a -> IO (Maybe a)
    run_pipeline p = runMaybeT (runReaderT p env)

withLocalTmpFS :: RunMakeM a -> RunMakeM a
withLocalTmpFS act =
  let initializer = do
        MakeEnv{..} <- ask
        lcl_tmpfs <- liftIO $ forkTmpFsFrom (cs_tmpfs cs_env)
        return $ cs_env { cs_tmpfs = lcl_tmpfs }
      finalizer lcl_env = do
        gbl_env <- ask
        liftIO $ mergeTmpFsInto (cs_tmpfs lcl_env) (cs_tmpfs (cs_env gbl_env))
  in MC.bracket initializer finalizer
     $ \lcl_cs_env -> local (\env -> env { cs_env = lcl_cs_env }) act

data MakeAction = forall a. MakeAction !(RunMakeM a) !(MVar (Maybe a))

waitMakeAction :: MakeAction -> IO ()
waitMakeAction (MakeAction _ mvar) = () <$ readMVar mvar
