{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Unit.State
  ( module CSlash.Unit.Info
  , module CSlash.Unit.State
  ) where

import Prelude hiding ((<>))

import CSlash.Driver.DynFlags

import CSlash.Platform
import CSlash.Platform.Ways

import CSlash.Unit.Database
import CSlash.Unit.Info
import CSlash.Unit.Ppr
import CSlash.Unit.Types
import CSlash.Unit.Module
import CSlash.Unit.Home

import CSlash.Types.Unique.FM
import CSlash.Types.Unique.DFM
import CSlash.Types.Unique.Set
import CSlash.Types.Unique.DSet
import CSlash.Types.Unique.Map
import CSlash.Types.Unique
import CSlash.Types.PkgQual

import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Outputable as Outputable
import CSlash.Data.Maybe

import System.Environment ( getEnv )
import CSlash.Data.FastString
import qualified GHC.Data.ShortText as ST
import CSlash.Utils.Logger
import CSlash.Utils.Error
import CSlash.Utils.Exception

import System.Directory
import System.FilePath as FilePath
import Control.Monad
import Data.Graph (stronglyConnComp, SCC(..))
import Data.Char ( toUpper )
import Data.List ( intersperse, partition, sortBy, isSuffixOf, sortOn )
import Data.Set (Set)
import Data.Monoid (First(..))
import qualified Data.Semigroup as Semigroup
import qualified Data.Set as Set
-- import GHC.LanguageExtensions
import Control.Applicative

data ModuleOrigin
  = ModHidden
  | ModUnusable !UnusableUnit
  | ModOrigin
    { fromOrigUnit :: Maybe Bool
    , fromExposedReexport :: [UnitInfo]
    , fromHiddenReexport :: [UnitInfo]
    , fromPackageFlag :: Bool
    }

data UnusableUnit = UnusableUnit
  { uuUnit :: !Unit
  , uuReason :: !UnusableUnitReason
  , uuIsReexport :: !Bool
  }

instance Outputable ModuleOrigin where
  ppr ModHidden = text "hidden module"
  ppr (ModUnusable _) = text "unusable module"
  ppr (ModOrigin e res rhs f) = sep (punctuate comma (
                                        (case e of
                                           Nothing -> []
                                           Just False -> [text "hidden package"]
                                           Just True -> [text "exposed package"])
                                        ++ (if null res
                                             then []
                                             else [text "reexported by" <+>
                                                   sep (map (ppr . mkUnit) res)])
                                        ++ (if null rhs
                                             then []
                                             else [text "hidden reexport by" <+>
                                                   sep (map (ppr . mkUnit) res)])
                                        ++ (if f then [text "package flag"] else [])))

fromExposedModules :: Bool -> ModuleOrigin
fromExposedModules e = ModOrigin (Just e) [] [] False

fromReexportedModules :: Bool -> UnitInfo -> ModuleOrigin
fromReexportedModules True pkg = ModOrigin Nothing [pkg] [] False
fromReexportedModules False pkg = ModOrigin Nothing [] [pkg] False

fromFlag :: ModuleOrigin
fromFlag = ModOrigin Nothing [] [] True

instance Semigroup ModuleOrigin where
  x@(ModOrigin e res rhs f) <> y@(ModOrigin e' res' rhs' f') =
    ModOrigin (g e e') (res ++ res') (rhs ++ rhs') (f || f')
    where
      g (Just b) (Just b')
        | b == b' = Just b
        | otherwise = pprPanic "ModOrigin: package both exposed/hidden" $
                      text "x: " <> ppr x $$ text "y: " <> ppr y
      g Nothing x = x
      g x Nothing = x

  x <> y = pprPanic "ModOrigin: module origin mismath" $
           text "x: " <> ppr x $$ text "y: " <> ppr y

instance Monoid ModuleOrigin where
  mempty = ModOrigin Nothing [] [] False
  mappend = (Semigroup.<>)

originVisible :: ModuleOrigin -> Bool
originVisible ModHidden = False
originVisible (ModUnusable _) = False
originVisible (ModOrigin b res _ f) = b == Just True || not (null res) || f

originEmpty :: ModuleOrigin -> Bool
originEmpty (ModOrigin Nothing [] [] False) = True
originEmpty _ = False

type PreloadUnitClosure = UniqSet UnitId

type VisibilityMap = UniqMap Unit UnitVisibility

data UnitVisibility = UnitVisibility
  { uv_expose_all :: Bool
  , uv_renamings :: [(ModuleName, ModuleName)]
  , uv_package_name :: First FastString
  , uv_requirements :: UniqMap ModuleName (Set InstantiatedModule)
  , uv_explicit :: Maybe PackageArg
  }

instance Outputable UnitVisibility where
  ppr (UnitVisibility
       { uv_expose_all = b
       , uv_renamings = rns
       , uv_package_name = First mb_pn
       , uv_requirements = reqs
       , uv_explicit = explicit
       }) = ppr (b, rns, mb_pn, reqs, explicit)

instance Semigroup UnitVisibility where
  uv1 <> uv2 = UnitVisibility
               { uv_expose_all = uv_expose_all uv1 || uv_expose_all uv2
               , uv_renamings = uv_renamings uv1 ++ uv_renamings uv2
               , uv_package_name = mappend (uv_package_name uv1) (uv_package_name uv2)
               , uv_requirements = plusUniqMap_C Set.union (uv_requirements uv2)
                                                           (uv_requirements uv1)
               , uv_explicit = uv_explicit uv1 <|> uv_explicit uv2
               }

instance Monoid UnitVisibility where
  mempty = UnitVisibility
           { uv_expose_all = False
           , uv_renamings = []
           , uv_package_name = First Nothing
           , uv_requirements = emptyUniqMap
           , uv_explicit = Nothing
           }
  mappend = (Semigroup.<>)

data UnitConfig = UnitConfig
  { unitConfigPlatformArchOS :: !ArchOS
  , unitConfigWays :: !Ways

  , unitConfigAllowVirtual :: !Bool

  , unitConfigProgramName :: !String

  , unitConfigGlobalDB :: !FilePath
  , unitConfigCSLDir :: !FilePath
  , unitConfigDBName :: !String

  , unitConfigAutoLink :: ![UnitId]
  , unitConfigHideAll :: !Bool

  , unitConfigDBCache :: Maybe [UnitDatabase UnitId]

  , unitConfigFlagsDB :: [PackageDBFlag]
  , unitConfigFlagsExposed :: [PackageFlag]
  , unitConfigFlagsIgnored :: [IgnorePackageFlag]
  , unitConfigHomeUnits :: Set.Set UnitId
  }

initUnitConfig :: DynFlags -> Maybe [UnitDatabase UnitId] -> Set.Set UnitId -> UnitConfig
initUnitConfig dflags cached_dbs home_units =
  let !hu_id = homeUnitId_ dflags
      !hu_instanceof = homeUnitInstanceOf_ dflags
      !hu_instantiations = homeUnitInstantiations_ dflags

      autoLink
        | not (gopt Opt_AutoLinkPackages dflags) = []
        | otherwise = filter (hu_id /=) [baseUnitId]

      allow_virtual_units = case (hu_instanceof, hu_instantiations) of
        (Just u, is) -> u == hu_id && any (isHoleModule . snd) is
        _ -> False

  in UnitConfig
     { unitConfigPlatformArchOS = platformArchOS (targetPlatform dflags)
     , unitConfigProgramName = programName dflags
     , unitConfigWays = ways dflags
     , unitConfigAllowVirtual = allow_virtual_units

     , unitConfigGlobalDB = globalPackageDatabasePath dflags
     , unitConfigCSLDir = topDir dflags
     , unitConfigDBName = "package.conf.d"

     , unitConfigAutoLink = autoLink
     , unitConfigHideAll = gopt Opt_HideAllPackages dflags

     , unitConfigDBCache = cached_dbs
     , unitConfigFlagsDB = map (offsetPackageDb (workingDirectory dflags)) $ packageDBFlags dflags
     , unitConfigFlagsExposed = packageFlags dflags
     , unitConfigFlagsIgnored = ignorePackageFlags dflags
     , unitConfigHomeUnits = home_units
     }
  where
    offsetPackageDb :: Maybe FilePath -> PackageDBFlag -> PackageDBFlag
    offsetPackageDb (Just offset) (PackageDB (PkgDbPath p)) | isRelative p
      = PackageDB (PkgDbPath (offset </> p))
    offsetPackageDb _ p = p

type ModuleNameProvidersMap = UniqMap ModuleName (UniqMap Module ModuleOrigin)

data UnitState = UnitState
  { unitInfoMap :: UnitInfoMap
  , preloadClosure :: PreloadUnitClosure
  , packageNameMap :: UniqFM PackageName UnitId
  , wireMap :: UniqMap UnitId UnitId
  , unwireMap :: UniqMap UnitId UnitId
  , preloadUnits :: [UnitId]
  , explicitUnits :: [(Unit, Maybe PackageArg)]
  , homeUnitDepends :: [UnitId]
  , moduleNameProvidersMap :: !ModuleNameProvidersMap
  , requirementContext :: UniqMap ModuleName [InstantiatedModule]
  , allowVirtualUnits :: !Bool
  }

emptyUnitState :: UnitState
emptyUnitState = UnitState
  { unitInfoMap = emptyUniqMap
  , preloadClosure = emptyUniqSet
  , packageNameMap = emptyUFM
  , wireMap = emptyUniqMap
  , unwireMap = emptyUniqMap
  , preloadUnits = []
  , explicitUnits = []
  , homeUnitDepends = []
  , moduleNameProvidersMap = emptyUniqMap
  , requirementContext = emptyUniqMap
  , allowVirtualUnits = False
  }

data UnitDatabase unit = UnitDatabase
  { unitDatabasePath :: FilePath
  , unitDatabaseUnits :: [GenUnitInfo unit]
  }

instance Outputable u => Outputable (UnitDatabase u) where
  ppr (UnitDatabase fp _) = text "DB:" <+> text fp

type UnitInfoMap = UniqMap UnitId UnitInfo

lookupUnit :: UnitState -> Unit -> Maybe UnitInfo
lookupUnit pkgs = lookupUnit' (allowVirtualUnits pkgs) (unitInfoMap pkgs) (preloadClosure pkgs)

lookupUnit' :: Bool -> UnitInfoMap -> PreloadUnitClosure -> Unit -> Maybe UnitInfo
lookupUnit' allowOnTheFlyInst pkg_map closure u = case u of
  HoleUnit -> error "Hole unit"
  RealUnit i -> lookupUniqMap pkg_map (unDefinite i)
  VirtUnit i
    | allowOnTheFlyInst
      -> fmap (renameUnitInfo pkg_map closure (instUnitInsts i))
         (lookupUniqMap pkg_map (instUnitInstanceOf i))
    | otherwise
      -> lookupUniqMap pkg_map (virtualUnitId i)

lookupUnitId :: UnitState -> UnitId -> Maybe UnitInfo
lookupUnitId state uid = lookupUnitId' (unitInfoMap state) uid

lookupUnitId' :: UnitInfoMap -> UnitId -> Maybe UnitInfo
lookupUnitId' db uid = lookupUniqMap db uid

unsafeLookupUnit :: HasDebugCallStack => UnitState -> Unit -> UnitInfo
unsafeLookupUnit state u = case lookupUnit state u of
  Just info -> info
  Nothing -> pprPanic "unsafeLookupUnit" (ppr u)

unsafeLookupUnitId :: HasDebugCallStack => UnitState -> UnitId -> UnitInfo
unsafeLookupUnitId state uid = case lookupUnitId state uid of
  Just info -> info
  Nothing -> pprPanic "unsafeLookupUnitId" (ppr uid)

mkUnitInfoMap :: [UnitInfo] -> UnitInfoMap
mkUnitInfoMap infos = foldl' add emptyUniqMap infos
  where
    mkVirt p = virtualUnitId (mkInstantiatedUnit (unitInstanceOf p) (unitInstantiations p))
    add pkg_map p
      | not (null (unitInstantiations p))
      = addToUniqMap (addToUniqMap pkg_map (mkVirt p) p) (unitId p) p
      | otherwise
      = addToUniqMap pkg_map (unitId p) p      

listUnitInfo :: UnitState -> [UnitInfo]
listUnitInfo state = nonDetEltsUniqMap (unitInfoMap state)

initUnits
  :: Logger
  -> DynFlags
  -> Maybe [UnitDatabase UnitId]
  -> Set.Set UnitId
  -> IO ([UnitDatabase UnitId], UnitState, HomeUnit, Maybe PlatformConstants)
initUnits logger dflags cached_dbs home_units = do
  let forceUnitInfoMap (state, _) = unitInfoMap state `seq` ()
  (unit_state, dbs) <- withTiming logger (text "initializing unit database")
                       forceUnitInfoMap $
                       mkUnitState logger (initUnitConfig dflags cached_dbs home_units)

  putDumpFileMaybe logger Opt_D_dump_mod_map "Module Map"
    FormatText (updSDocContext (\ctx -> ctx { sdocLineLength = 200 })
                $ pprModuleMap (moduleNameProvidersMap unit_state))

  let home_unit = mkHomeUnit unit_state
                             (homeUnitId_ dflags)
                             (homeUnitInstanceOf_ dflags)
                             (homeUnitInstantiations_ dflags)

  mconstants <- return Nothing

  return (dbs, unit_state, home_unit, mconstants)

mkHomeUnit
  :: UnitState
  -> UnitId
  -> Maybe UnitId
  -> [(ModuleName, Module)]
  -> HomeUnit
mkHomeUnit unit_state hu_id hu_instanceof hu_instantiations_ =
  let wmap = wireMap unit_state
      hu_instantiations = map (fmap (upd_wired_in_mod wmap)) hu_instantiations_
  in case (hu_instanceof, hu_instantiations) of
       (Nothing, []) -> DefiniteHomeUnit hu_id Nothing
       (Nothing, _) -> throwCsException $
                       CmdLineError ("Use of -instantiated-with requires -this-component-id")
       (Just _, []) -> throwCsException $
                       CmdLineError ("Use -this-component-id requires -instantiated-with")
       (Just u, is)
         | all (isHoleModule . snd) is && u == hu_id
           -> IndefiniteHomeUnit u is
         | otherwise
           -> DefiniteHomeUnit hu_id (Just (u, is))

-- -----------------------------------------------------------------------------
-- Reading the unit database(s)

readUnitDatabases :: Logger -> UnitConfig -> IO [UnitDatabase UnitId]
readUnitDatabases logger cfg = do
  conf_refs <- getUnitDbRefs cfg
  confs <- liftM catMaybes $ mapM (resolveUnitDatabase cfg) conf_refs
  mapM (readUnitDatabase logger cfg) confs

getUnitDbRefs :: UnitConfig -> IO [PkgDbRef]
getUnitDbRefs cfg = do
    let system_conf_refs = [UserPkgDb, GlobalPkgDb]

    e_pkg_path <- tryIO (getEnv $ map toUpper (unitConfigProgramName cfg) ++ "_PACKAGE_PATH")
    let base_conf_refs = case e_pkg_path of
                           Left _ -> system_conf_refs
                           Right path
                             | Just (xs, x) <- snocView path, isSearchPathSeparator x
                               -> map PkgDbPath (splitSearchPath xs) ++ system_conf_refs
                             | otherwise
                               -> map PkgDbPath (splitSearchPath path)

    return $ reverse $ foldr doFlag base_conf_refs (unitConfigFlagsDB cfg)
  where
    doFlag (PackageDB p) dbs = p : dbs
    doFlag NoUserPackageDB dbs = filter isNotUser dbs
    doFlag NoGlobalPackageDB dbs = filter isNotGlobal dbs
    doFlag ClearPackageDBs _ = []

    isNotUser UserPkgDb = False
    isNotUser _ = True

    isNotGlobal GlobalPkgDb = False
    isNotGlobal _ = True

resolveUnitDatabase :: UnitConfig -> PkgDbRef -> IO (Maybe FilePath)
resolveUnitDatabase cfg GlobalPkgDb = return $ Just (unitConfigGlobalDB cfg)
resolveUnitDatabase cfg UserPkgDb = runMaybeT $ do
  dir <- versionedAppDir (unitConfigProgramName cfg) (unitConfigPlatformArchOS cfg)
  let pkgconf = dir </> unitConfigDBName cfg
  exists <- tryMaybeT $ doesDirectoryExist pkgconf
  if exists then return pkgconf else mzero
resolveUnitDatabase _ (PkgDbPath name) = return $ Just name

readUnitDatabase :: Logger -> UnitConfig -> FilePath -> IO (UnitDatabase UnitId)
readUnitDatabase logger cfg conf_file = do
  isdir <- doesDirectoryExist conf_file

  proto_pkg_configs <-
    if isdir
    then readDirStyleUnitInfo conf_file
    else throwCsExceptionIO $ InstallationError $
         "can't find a package database at " ++ conf_file

  let conf_file' = dropTrailingPathSeparator conf_file
      top_dir = unitConfigCSLDir cfg
      pkgroot = takeDirectory conf_file'
      pkg_configs1 = map (mungeUnitInfo top_dir pkgroot . mapUnitInfo (\(UnitKey x) -> UnitId x)
                          . mkUnitKeyInfo) proto_pkg_configs

  return $ UnitDatabase conf_file' pkg_configs1

  where
    readDirStyleUnitInfo conf_dir = do
      let filename = conf_dir </> "package.cache"
      cache_exists <- doesFileExist filename
      if cache_exists
        then do debugTraceMsg logger 2 $ text "Using binary package database:" <+> text filename
                readPackageDbForCs filename
        else do debugTraceMsg logger 2 $ text "There is no package.cache in"
                  <+> text conf_dir
                  <> text ", checking if the database is empty"
                db_empty <- all (not . isSuffixOf ".conf")
                            <$> getDirectoryContents conf_dir
                if db_empty
                  then do debugTraceMsg logger 3 $ text "There are no .conf files in"
                            <+> text conf_dir <> text ", treating"
                            <+> text "package database as empty"
                          return []
                  else throwCsExceptionIO $ InstallationError $
                       "there is no package.cache in " ++ conf_dir ++
                       " even though package database is not empty"        

mungeUnitInfo :: FilePath -> FilePath -> UnitInfo -> UnitInfo
mungeUnitInfo top_dir pkgroot =
    mungeDynLibFields
  . mungeUnitInfoPaths (ST.pack top_dir) (ST.pack pkgroot)

mungeDynLibFields :: UnitInfo -> UnitInfo
mungeDynLibFields pkg = pkg
  { unitLibraryDynDirs = case unitLibraryDynDirs pkg of
                           [] -> unitLibraryDirs pkg
                           ds -> ds
  } 

-- -----------------------------------------------------------------------------
-- Modify our copy of the unit database based flags

applyPackageFlag
  :: UnitPrecedenceMap
  -> UnitInfoMap
  -> PreloadUnitClosure
  -> UnusableUnits
  -> Bool
  -> [UnitInfo]
  -> VisibilityMap
  -> PackageFlag
  -> MaybeErr UnitErr VisibilityMap
applyPackageFlag prec_map pkg_map closure unusable no_hide_others pkgs vm flag =
  case flag of
    ExposePackage _ arg (ModRenaming b rns) ->
      case findPackages prec_map pkg_map closure arg pkgs unusable of
        Left ps -> Failed (PackageFlagErr flag ps)
        Right (p:_) -> Succeeded vm'
          where
            n = fsPackageName p
            reqs | UnitIdArg orig_uid <- arg = collectHoles orig_uid
                 | otherwise = emptyUniqMap
            collectHoles uid = case uid of
              HoleUnit -> emptyUniqMap
              RealUnit{} -> emptyUniqMap
              VirtUnit indef ->
                let local = [ unitUniqMap (moduleName mod)
                                          (Set.singleton $ Module indef mod_name)
                            | (mod_name, mod) <- instUnitInsts indef
                            , isHoleModule mod
                            ]
                    recurse = [ collectHoles (moduleUnit mod)
                              | (_, mod) <- instUnitInsts indef
                              ]
                in plusUniqMapListWith Set.union $ local ++ recurse
            uv = UnitVisibility
                 { uv_expose_all = b
                 , uv_renamings = rns
                 , uv_package_name = First (Just n)
                 , uv_requirements = reqs
                 , uv_explicit = Just arg
                 }
            vm' = addToUniqMap_C mappend vm_cleared (mkUnit p) uv
            vm_cleared
              | no_hide_others = vm
              | (_:_) <- rns = vm
              | otherwise = filterWithKeyUniqMap
                            (\k uv -> k == mkUnit p
                                      || First (Just n) /= uv_package_name uv) vm
        _ -> panic "applyPackageFlag"

    HidePackage str ->
      case findPackages prec_map pkg_map closure (PackageArg str) pkgs unusable of
        Left ps -> Failed (PackageFlagErr flag ps)
        Right ps -> Succeeded $ foldl' delFromUniqMap vm (map mkUnit ps)

findPackages
  :: UnitPrecedenceMap
  -> UnitInfoMap
  -> PreloadUnitClosure
  -> PackageArg
  -> [UnitInfo]
  -> UnusableUnits
  -> Either [(UnitInfo, UnusableUnitReason)] [UnitInfo]
findPackages prec_map pkg_map closure arg pkgs unusable
  = let ps = mapMaybe (finder arg) pkgs
        finder (PackageArg str) p
          = if matchingStr str p
            then Just p
            else Nothing
        finder (UnitIdArg uid) p
          = case uid of
              RealUnit (Definite iuid)
                | iuid == unitId p
                  -> Just p
              VirtUnit inst
                | instUnitInstanceOf inst == unitId p
                  -> Just (renameUnitInfo pkg_map closure (instUnitInsts inst) p)
              _ -> Nothing
    in if null ps
       then Left (mapMaybe (\(x, y) -> finder arg x >>= \x' -> return (x', y))
                  (nonDetEltsUniqMap unusable))
       else Right (sortByPreference prec_map ps)

renameUnitInfo
  :: UnitInfoMap -> PreloadUnitClosure -> [(ModuleName, Module)] -> UnitInfo -> UnitInfo
renameUnitInfo pkg_map closure insts conf =
  let hsubst = listToUFM insts
      smod = renameHoleModule' pkg_map closure hsubst
      new_insts = map (\(k, v) -> (k, smod v)) (unitInstantiations conf)
  in conf
     { unitInstantiations = new_insts
     , unitExposedModules = map (\(mod_name, mb_mod) -> (mod_name, fmap smod mb_mod))
                            (unitExposedModules conf)
     }

matchingStr :: String -> UnitInfo -> Bool
matchingStr str p
  = str == unitPackageIdString p
  || str == unitPackageNameString p

sortByPreference :: UnitPrecedenceMap -> [UnitInfo] -> [UnitInfo]
sortByPreference prec_map = sortBy (flip (compareByPreference prec_map))

compareByPreference
  :: UnitPrecedenceMap
  -> UnitInfo
  -> UnitInfo
  -> Ordering
compareByPreference prec_map pkg pkg'
  = case comparing unitPackageVersion pkg pkg' of
      GT -> GT
      EQ | Just prec <- lookupUniqMap prec_map (unitId pkg)
         , Just prec' <- lookupUniqMap prec_map (unitId pkg')
           -> compare prec prec'
         | otherwise
           -> EQ
      LT -> LT

comparing :: Ord a => (t -> a) -> t -> t -> Ordering
comparing f a b = f a `compare` f b

pprFlag :: PackageFlag -> SDoc
pprFlag flag = case flag of
  HidePackage p -> text "-hide-package " <> text p
  ExposePackage doc _ _ -> text doc

-- -----------------------------------------------------------------------------
-- Wired-in units

type WiringMap = UniqMap UnitId UnitId

findWiredInUnits
  :: Logger
  -> UnitPrecedenceMap
  -> [UnitInfo]
  -> VisibilityMap
  -> IO ([UnitInfo], WiringMap)
findWiredInUnits logger prec_map pkgs vis_map = do
  let matches :: UnitInfo -> UnitId -> Bool
      matches pc pid = unitPackageName pc == PackageName (unitIdFS pid)

      findWiredInUnit :: [UnitInfo] -> UnitId -> IO (Maybe (UnitId, UnitInfo))
      findWiredInUnit pkgs wired_pkg = firstJustsM [try all_exposed_ps, try all_ps, notfound]
        where
          all_ps = [ p | p <- pkgs, p `matches` wired_pkg ]
          all_exposed_ps = [ p | p <- all_ps, (mkUnit p) `elemUniqMap` vis_map ]

          try ps = case sortByPreference prec_map ps of
                     p:_ -> Just <$> pick p
                     _ -> pure Nothing
          notfound = do
            debugTraceMsg logger 2 $ text "wired-in package "
                                     <> ftext (unitIdFS wired_pkg)
                                     <> text " not found."
            return Nothing

          pick :: UnitInfo -> IO (UnitId, UnitInfo)
          pick pkg = do
            debugTraceMsg logger 2 $ text "wired-in package "
                                     <> ftext (unitIdFS wired_pkg)
                                     <> text " mapped to "
                                     <> ppr (unitId pkg)
            return (wired_pkg, pkg)

  mb_wired_in_pkgs <- mapM (findWiredInUnit pkgs) wiredInUnitIds

  let wired_in_pkgs = catMaybes mb_wired_in_pkgs

      wiredInMap :: UniqMap UnitId UnitId
      wiredInMap = listToUniqMap
        [ (unitId realUnitInfo, wiredInUnitId)
        | (wiredInUnitId, realUnitInfo) <- wired_in_pkgs
        , not (unitIsIndefinite realUnitInfo)
        ]

      updateWiredInDependencies pkgs = map (upd_deps . upd_pkg) pkgs
        where
          upd_pkg pkg
            | Just wiredInUnitId <- lookupUniqMap wiredInMap (unitId pkg)
            = pkg { unitId = wiredInUnitId
                  , unitInstanceOf = wiredInUnitId
                  }
            | otherwise
            = pkg

          upd_deps pkg = pkg
            { unitDepends = map (upd_wired_in wiredInMap) (unitDepends pkg)
            , unitExposedModules = map (\(k, v) -> (k, fmap (upd_wired_in_mod wiredInMap) v))
                                       (unitExposedModules pkg)
            }

  return (updateWiredInDependencies pkgs, wiredInMap)

upd_wired_in_mod :: WiringMap -> Module -> Module
upd_wired_in_mod wiredInMap (Module uid m) = Module (upd_wired_in_uid wiredInMap uid) m

upd_wired_in_uid :: WiringMap -> Unit -> Unit
upd_wired_in_uid wiredInMap u = case u of
  HoleUnit -> HoleUnit
  RealUnit (Definite uid) -> RealUnit (Definite (upd_wired_in wiredInMap uid))
  VirtUnit indef_uid ->
    VirtUnit $ mkInstantiatedUnit
    (instUnitInstanceOf indef_uid)
    (map (\(x, y) -> (x, upd_wired_in_mod wiredInMap y)) (instUnitInsts indef_uid))

upd_wired_in :: WiringMap -> UnitId -> UnitId
upd_wired_in wiredInMap key
  | Just key' <- lookupUniqMap wiredInMap key = key'
  | otherwise = key

updateVisibilityMap :: WiringMap -> VisibilityMap -> VisibilityMap
updateVisibilityMap wiredInMap vis_map = foldl' f vis_map (nonDetUniqMapToList wiredInMap)
  where f vm (from, to) = case lookupUniqMap vis_map (RealUnit (Definite from)) of
                    Nothing -> vm
                    Just r -> addToUniqMap (delFromUniqMap vm (RealUnit (Definite from)))
                              (RealUnit (Definite to)) r


-- ----------------------------------------------------------------------------

data UnusableUnitReason
  = IgnoredWithFlag
  | BrokenDependencies [UnitId]
  | CyclicDependencies [UnitId]
  | IgnoredDependencies [UnitId]
  | ShadowedDependencies [UnitId]

instance Outputable UnusableUnitReason where
  ppr IgnoredWithFlag = text "[ignored with flag]"
  ppr (BrokenDependencies uids) = brackets (text "broken" <+> ppr uids)
  ppr (CyclicDependencies uids) = brackets (text "cyclic" <+> ppr uids)
  ppr (IgnoredDependencies uids) = brackets (text "ignored" <+> ppr uids)
  ppr (ShadowedDependencies uids) = brackets (text "shadowed" <+> ppr uids)

type UnusableUnits = UniqMap UnitId (UnitInfo, UnusableUnitReason)

pprReason :: SDoc -> UnusableUnitReason -> SDoc
pprReason pref reason = case reason of
  IgnoredWithFlag -> pref <+> text "ignored due to an -ignore-package flag"
  BrokenDependencies deps -> pref <+> text "unusable due to missing dependencies:"
                             $$ nest 2 (hsep (map ppr deps))
  CyclicDependencies deps -> pref <+> text "unusable due to cyclic dependencies:"
                             $$ nest 2 (hsep (map ppr deps))
  IgnoredDependencies deps -> pref <+> text ("unusable beacuse the -ignore-package flags was used"
                                             ++ "to ignore at least one of its dependencies:")
                              $$ nest 2 (hsep (map ppr deps))
  ShadowedDependencies deps -> pref <+> text "unusable due to shadowed dependencies:"
                               $$ nest 2 (hsep (map ppr deps))

reportCycles :: Logger -> [SCC UnitInfo] -> IO ()
reportCycles logger sccs = mapM_ report sccs
  where
    report (AcyclicSCC _) = return ()
    report (CyclicSCC vs) = debugTraceMsg logger 2 $
                            text "these packages are involved in a cycle:" $$
                            nest 2 (hsep (map (ppr . unitId) vs))

reportUnusable :: Logger -> UnusableUnits -> IO ()
reportUnusable logger pkgs = mapM_ report (nonDetUniqMapToList pkgs)
  where
    report (ipid, (_, reason)) = debugTraceMsg logger 2 $
                                 pprReason (text "package" <+> ppr ipid <+> text "is") reason

-- ----------------------------------------------------------------------------
--
-- Utilities on the database
--

type RevIndex = UniqMap UnitId [UnitId]

reverseDeps :: UnitInfoMap -> RevIndex
reverseDeps db = nonDetFoldUniqMap go emptyUniqMap db
  where
    go :: (UnitId, UnitInfo) -> RevIndex -> RevIndex
    go (_, pkg) r = foldl' (go' (unitId pkg)) r (unitDepends pkg)

    go' from r to = addToUniqMap_C (++) r to [from]

removeUnits
  :: [UnitId]
  -> RevIndex
  -> UnitInfoMap
  -> (UnitInfoMap, [UnitInfo])
removeUnits uids index m = go uids (m, [])
  where
    go [] (m, pkgs) = (m, pkgs)
    go (uid:uids) (m, pkgs)
      | Just pkg <- lookupUniqMap m uid
      = case lookupUniqMap index uid of
          Nothing -> go uids (delFromUniqMap m uid, pkg:pkgs)
          Just rdeps -> go (rdeps ++ uids) (delFromUniqMap m uid, pkg:pkgs)
      | otherwise
      = go uids (m, pkgs)

depsNotAvailable
  :: UnitInfoMap
  -> UnitInfo
  -> [UnitId]
depsNotAvailable pkg_map pkg = filter (not . (`elemUniqMap` pkg_map)) (unitDepends pkg)

depsAbiMismatch
  :: UnitInfoMap
  -> UnitInfo
  -> [UnitId]
depsAbiMismatch pkg_map pkg = map fst . filter (not . abiMatch) $ unitAbiDepends pkg
  where
    abiMatch (dep_uid, abi)
      | Just dep_pkg <- lookupUniqMap pkg_map dep_uid
      = unitAbiHash dep_pkg == abi
      | otherwise
      = False

-- -----------------------------------------------------------------------------
-- Ignore units

ignoreUnits :: [IgnorePackageFlag] -> [UnitInfo] -> UnusableUnits
ignoreUnits flags pkgs = listToUniqMap (concatMap doit flags)
  where
    doit (IgnorePackage str) = case partition (matchingStr str) pkgs of
                                 (ps, _) -> [ (unitId p, (p, IgnoredWithFlag))
                                            | p <- ps
                                            ]

-- ----------------------------------------------------------------------------
--
-- Merging databases
--

type UnitPrecedenceMap = UniqMap UnitId Int

mergeDatabases
  :: Logger
  -> [UnitDatabase UnitId]
  -> IO (UnitInfoMap, UnitPrecedenceMap)
mergeDatabases logger = foldM merge (emptyUniqMap, emptyUniqMap) . zip [1..]
  where
    merge (pkg_map, prec_map) (i, UnitDatabase db_path db) = do
      debugTraceMsg logger 2 $
        text "loading package database" <+> text db_path
      forM_ (Set.toList override_set) $ \pkg ->
        debugTraceMsg logger 2 $
        text "package" <+> ppr pkg <+>
        text "overrides a previously defined package"
      return (pkg_map', prec_map')
      where
        db_map = mk_pkg_map db
        mk_pkg_map = listToUniqMap . map (\p -> (unitId p, p))

        override_set :: Set UnitId
        override_set = Set.intersection (nonDetUniqMapToKeySet db_map)
                                        (nonDetUniqMapToKeySet pkg_map)

        pkg_map' :: UnitInfoMap
        pkg_map' = pkg_map `plusUniqMap` db_map
      
        prec_map' :: UnitPrecedenceMap
        prec_map' = prec_map `plusUniqMap` (mapUniqMap (const i) db_map)

validateDatabase
  :: UnitConfig
  -> UnitInfoMap
  -> (UnitInfoMap, UnusableUnits, [SCC UnitInfo])
validateDatabase cfg pkg_map1 = (pkg_map5, unusable, sccs)
  where
    ignore_flags = reverse (unitConfigFlagsIgnored cfg)

    index = reverseDeps pkg_map1

    mk_unusable mk_err dep_matcher m uids =
      listToUniqMap [ (unitId pkg, (pkg, mk_err (dep_matcher m pkg)))
                    | pkg <- uids
                    ]

    directly_broken = filter (not . null . depsNotAvailable pkg_map1)
                            (nonDetEltsUniqMap pkg_map1)

    (pkg_map2, broken) = removeUnits (map unitId directly_broken) index pkg_map1
    unusable_broken = mk_unusable BrokenDependencies depsNotAvailable pkg_map2 broken

    sccs = stronglyConnComp [ (pkg, unitId pkg, unitDepends pkg)
                            | pkg <- nonDetEltsUniqMap pkg_map2
                            ]

    getCyclicSCC (CyclicSCC vs) = map unitId vs
    getCyclicSCC (AcyclicSCC _) = []

    (pkg_map3, cyclic) = removeUnits (concatMap getCyclicSCC sccs) index pkg_map2
    unusable_cyclic = mk_unusable CyclicDependencies depsNotAvailable pkg_map3 cyclic

    directly_ignored = ignoreUnits ignore_flags (nonDetEltsUniqMap pkg_map3)
    (pkg_map4, ignored) = removeUnits (nonDetKeysUniqMap directly_ignored) index pkg_map3
    unusable_ignored = mk_unusable IgnoredDependencies depsNotAvailable pkg_map4 ignored

    directly_shadowed = filter (not . null . depsAbiMismatch pkg_map4)
                               (nonDetEltsUniqMap pkg_map4)
    (pkg_map5, shadowed) = removeUnits (map unitId directly_shadowed) index pkg_map4
    unusable_shadowed = mk_unusable ShadowedDependencies depsAbiMismatch pkg_map5 shadowed

    unusable = plusUniqMapList [ unusable_shadowed
                               , unusable_cyclic
                               , unusable_broken
                               , unusable_ignored
                               , directly_ignored
                               ]                      

-- -----------------------------------------------------------------------------

mkUnitState
  :: Logger
  -> UnitConfig
  -> IO (UnitState, [UnitDatabase UnitId])
mkUnitState logger cfg = do
  raw_dbs <- case unitConfigDBCache cfg of
               Nothing -> readUnitDatabases logger cfg
               Just dbs -> return dbs
  let dbs = raw_dbs

  let raw_other_flags = reverse (unitConfigFlagsExposed cfg)
      (hpt_flags, other_flags)
        = partition (selectHptFlag (unitConfigHomeUnits cfg)) raw_other_flags

  debugTraceMsg logger 2 $ text "package flags" <+> ppr other_flags

  let home_unit_deps = selectHomeUnits (unitConfigHomeUnits cfg) hpt_flags

  (pkg_map1, prec_map) <- mergeDatabases logger dbs

  let (pkg_map2, unusable, sccs) = validateDatabase cfg pkg_map1

  reportCycles logger sccs
  reportUnusable logger unusable

  let pkgs1 = sortByPreference prec_map $ nonDetEltsUniqMap pkg_map2

  let prelim_pkg_db = mkUnitInfoMap pkgs1

  let preferLater unit unit' =
        case compareByPreference prec_map unit unit' of
          GT -> unit
          _ -> unit'
      addIfMorePreferable m unit = addToUDFM_C preferLater m (fsPackageName unit) unit
      mostPreferablePackageReps = if unitConfigHideAll cfg
                                  then emptyUDFM
                                  else foldl' addIfMorePreferable emptyUDFM pkgs1
      mostPreferable u =
        case lookupUDFM mostPreferablePackageReps (fsPackageName u) of
          Nothing -> False
          Just u' -> compareByPreference prec_map u u' == EQ
      vis_map1 = foldl' (\vm p -> if unitIsExposed p
                                     && unitIsDefinite (mkUnit p)
                                     && mostPreferable p
                                  then addToUniqMap vm (mkUnit p)
                                       UnitVisibility
                                       { uv_expose_all = True
                                       , uv_renamings = []
                                       , uv_package_name = First (Just (fsPackageName p))
                                       , uv_requirements = emptyUniqMap
                                       , uv_explicit = Nothing
                                       }
                                  else vm)
                        emptyUniqMap pkgs1

  vis_map2 <- mayThrowUnitErr $ foldM
              (applyPackageFlag prec_map prelim_pkg_db emptyUniqSet unusable
               (unitConfigHideAll cfg) pkgs1)
              vis_map1
              other_flags

  (pkgs2, wired_map) <- findWiredInUnits logger prec_map pkgs1 vis_map2
  let pkg_db = mkUnitInfoMap pkgs2

      vis_map = updateVisibilityMap wired_map vis_map2

      pkgname_map = listToUFM [ (unitPackageName p, unitInstanceOf p)
                              | p <- pkgs2
                              ]

      explicit_pkgs = [(k, uv_explicit v) | (k, v) <- nonDetUniqMapToList vis_map]
      req_ctx = mapUniqMap (Set.toList) $
                plusUniqMapListWith Set.union (map uv_requirements (nonDetEltsUniqMap vis_map))

      preload1 = nonDetKeysUniqMap (filterUniqMap (isJust . uv_explicit) vis_map)

      basicLinkedUnits = fmap (RealUnit . Definite) $
                         filter (flip elemUniqMap pkg_db) $
                         unitConfigAutoLink cfg
      preload3 = ordNub $ (basicLinkedUnits ++ preload1)

  dep_preload <- mayThrowUnitErr $
                 closeUnitDeps pkg_db $
                 zip (map toUnitId preload3) (repeat Nothing)

  let mod_map1 = mkModuleNameProvidersMap logger cfg pkg_db emptyUniqSet vis_map
      mod_map2 = mkUnusableModuleNameProvidersMap unusable
      mod_map = mod_map2 `plusUniqMap` mod_map1

      !state = UnitState
               { preloadUnits = dep_preload
               , explicitUnits = explicit_pkgs
               , homeUnitDepends = Set.toList home_unit_deps
               , unitInfoMap = pkg_db
               , preloadClosure = emptyUniqSet
               , moduleNameProvidersMap = mod_map
               , packageNameMap = pkgname_map
               , wireMap = wired_map
               , unwireMap = listToUniqMap [ (v, k) | (k, v) <- nonDetUniqMapToList wired_map ]
               , requirementContext = req_ctx
               , allowVirtualUnits = unitConfigAllowVirtual cfg
               }
  return (state, raw_dbs)

selectHptFlag :: Set.Set UnitId -> PackageFlag -> Bool
selectHptFlag home_units (ExposePackage _ (UnitIdArg uid) _)
  | toUnitId uid `Set.member` home_units = True
selectHptFlag _ _ = False

selectHomeUnits :: Set.Set UnitId -> [PackageFlag] -> Set.Set UnitId
selectHomeUnits home_units flags = foldl' go Set.empty flags
  where
    go :: Set.Set UnitId -> PackageFlag -> Set.Set UnitId
    go cur (ExposePackage _ (UnitIdArg uid) _)
      | toUnitId uid `Set.member` home_units = Set.insert (toUnitId uid) cur
    go cur _ = cur

-- -----------------------------------------------------------------------------
-- Makes the mapping from ModuleName to package info

mkModuleNameProvidersMap
  :: Logger
  -> UnitConfig
  -> UnitInfoMap
  -> PreloadUnitClosure
  -> VisibilityMap
  -> ModuleNameProvidersMap
mkModuleNameProvidersMap logger cfg pkg_map closure vis_map =
  nonDetFoldUniqMap extend_modmap emptyMap vis_map_extended
  where
    vis_map_extended = default_vis `plusUniqMap` vis_map

    default_vis = listToUniqMap
      [ (mkUnit pkg, mempty)
      | (_, pkg) <- nonDetUniqMapToList pkg_map
      , unitIsIndefinite pkg || null (unitInstantiations pkg)
      ]

    emptyMap = emptyUniqMap
    setOrigins m os = fmap (const os) m
    extend_modmap (uid, UnitVisibility { uv_expose_all = b, uv_renamings = rns }) modmap
      = addListTo modmap theBindings
      where
        pkg = unit_lookup uid

        theBindings :: [(ModuleName, UniqMap Module ModuleOrigin)]
        theBindings = newBindings b rns

        newBindings
          :: Bool
          -> [(ModuleName, ModuleName)]
          -> [(ModuleName, UniqMap Module ModuleOrigin)]
        newBindings e rns = es e ++ hiddens ++ map rnBinding rns

        rnBinding
          :: (ModuleName, ModuleName) -> (ModuleName, UniqMap Module ModuleOrigin)
        rnBinding (orig, new) = (new, setOrigins origEntry fromFlag)
          where origEntry = case lookupUFM esmap orig of
                              Just r -> r
                              Nothing -> throwCsException
                                         (CmdLineError
                                          (renderWithContext
                                           (log_default_user_context
                                            (logFlags logger))
                                           (text "package flag: could not find module name"
                                            <+> ppr orig <+> text "in package" <+> ppr pk)))

        es :: Bool -> [(ModuleName, UniqMap Module ModuleOrigin)]
        es e = do
          (m, exposedReexport) <- exposed_mods
          let (pk', m', origin') = case exposedReexport of
                                     Nothing -> (pk, m, fromExposedModules e)
                                     Just (Module pk' m') ->
                                       (pk', m', fromReexportedModules e pkg)
          return (m, mkModMap pk' m' origin')

        esmap :: UniqFM ModuleName (UniqMap Module ModuleOrigin)
        esmap = listToUFM (es False)

        hiddens = [(m, mkModMap pk m ModHidden) | m <- hidden_mods]

        pk = mkUnit pkg

        unit_lookup uid = lookupUnit' (unitConfigAllowVirtual cfg) pkg_map closure uid
                          `orElse` pprPanic "unit_lookup" (ppr uid)

        exposed_mods = unitExposedModules pkg
        hidden_mods = unitHiddenModules pkg

mkUnusableModuleNameProvidersMap :: UnusableUnits -> ModuleNameProvidersMap
mkUnusableModuleNameProvidersMap unusables =
  nonDetFoldUniqMap extend_modmap emptyUniqMap unusables
  where
    extend_modmap (_, (unit_info, reason)) modmap = addListTo modmap bindings
      where
        bindings :: [(ModuleName, UniqMap Module ModuleOrigin)]
        bindings = exposed ++ hidden

        origin_reexport = ModUnusable (UnusableUnit unit reason True)
        origin_normal = ModUnusable (UnusableUnit unit reason False)
        unit = mkUnit unit_info

        exposed = map get_exposed exposed_mods
        hidden = [(m, mkModMap unit m origin_normal) | m <- hidden_mods]

        get_exposed (mod, Just _) = (mod , mkModMap unit mod origin_reexport)
        get_exposed (mod, _) = (mod, mkModMap unit mod origin_normal)

        exposed_mods = unitExposedModules unit_info
        hidden_mods = unitHiddenModules unit_info

addListTo
  :: (Monoid a, Ord k1, Ord k2, Uniquable k1, Uniquable k2)
  => UniqMap k1 (UniqMap k2 a)
  -> [(k1, UniqMap k2 a)]
  -> UniqMap k1 (UniqMap k2 a)
addListTo = foldl' merge
  where
    merge m (k, v) = addToUniqMap_C (plusUniqMap_C mappend) m k v

mkModMap :: Unit -> ModuleName -> ModuleOrigin -> UniqMap Module ModuleOrigin
mkModMap pkg mod = unitUniqMap (mkModule pkg mod)

-- -----------------------------------------------------------------------------
-- Package Utils

data LookupResult
  = LookupFound Module (UnitInfo, ModuleOrigin)
  | LookupMultiple [(Module, ModuleOrigin)]
  | LookupHidden [(Module, ModuleOrigin)] [(Module, ModuleOrigin)]
  | LookupUnusable [(Module, ModuleOrigin)]
  | LookupNotFound [ModuleSuggestion]

data ModuleSuggestion
  = SuggestVisible ModuleName Module ModuleOrigin
  | SuggestHidden ModuleName Module ModuleOrigin

lookupModuleWithSuggestions :: UnitState -> ModuleName -> PkgQual -> LookupResult
lookupModuleWithSuggestions pkgs
  = lookupModuleWithSuggestions' pkgs (moduleNameProvidersMap pkgs)

lookupModuleWithSuggestions'
  :: UnitState -> ModuleNameProvidersMap -> ModuleName -> PkgQual -> LookupResult
lookupModuleWithSuggestions' pkgs mod_map m mb_pn
  = case lookupUniqMap mod_map m of
      Nothing -> LookupNotFound suggestions
      Just xs -> case foldl' classify ([], [], [], []) (sortOn fst $ nonDetUniqMapToList xs) of
        ([], [], [], []) -> LookupNotFound suggestions
        (_, _, _, [(m,o)]) -> LookupFound m (mod_unit m, o)
        (_, _, _, exposed@(_:_)) -> LookupMultiple exposed
        ([], [], unusable@(_:_), []) -> LookupUnusable unusable
        (hidden_pkg, hidden_mod, _, []) -> LookupHidden hidden_pkg hidden_mod
  where
    classify (hidden_pkg, hidden_mod, unusable, exposed) (m, origin0) =
      let origin = filterOrigin mb_pn (mod_unit m) origin0
          x = (m, origin)
      in case origin of
           ModHidden
             -> (hidden_pkg, x:hidden_mod, unusable, exposed)
           ModUnusable _
             -> (hidden_pkg, hidden_mod, x:unusable, exposed)
           _ | originEmpty origin
             -> (hidden_pkg, hidden_mod, unusable, exposed)
             | originVisible origin
             -> (hidden_pkg, hidden_mod, unusable, x:exposed)
             | otherwise
             -> (x:hidden_pkg, hidden_mod, unusable, exposed)

    unit_lookup p = lookupUnit pkgs p `orElse`
                    pprPanic "lookupModuleWithSuggestions" (ppr p <+> ppr m)

    mod_unit = unit_lookup . moduleUnit

    filterOrigin :: PkgQual -> UnitInfo -> ModuleOrigin -> ModuleOrigin
    filterOrigin NoPkgQual _ o = o
    filterOrigin (ThisPkg _) _ o = o
    filterOrigin (OtherPkg u) pkg o =
      let match_pkg p = u == unitId p
      in case o of
           ModHidden
             | match_pkg pkg -> ModHidden
             | otherwise -> mempty
           ModUnusable _
             | match_pkg pkg -> o
             | otherwise -> mempty
           ModOrigin { fromOrigUnit = e, fromExposedReexport = res, fromHiddenReexport = rhs }
             -> ModOrigin
                { fromOrigUnit = if match_pkg pkg then e else Nothing
                , fromExposedReexport = filter match_pkg res
                , fromHiddenReexport = filter match_pkg rhs
                , fromPackageFlag = False
                }

    suggestions = fuzzyLookup (moduleNameString m) all_mods

    all_mods :: [(String, ModuleSuggestion)]
    all_mods = sortBy (comparing fst) $
      [ (moduleNameString m, suggestion)
      | (m, e) <- nonDetUniqMapToList (moduleNameProvidersMap pkgs)
      , suggestion <- map (getSuggestion m) (nonDetUniqMapToList e)
      ]

    getSuggestion name (mod, origin) =
      (if originVisible origin then SuggestVisible else SuggestHidden)
      name mod origin

closeUnitDeps :: UnitInfoMap -> [(UnitId, Maybe UnitId)] -> MaybeErr UnitErr [UnitId]
closeUnitDeps pkg_map ps = closeUnitDeps' pkg_map [] ps

closeUnitDeps' :: UnitInfoMap -> [UnitId] -> [(UnitId, Maybe UnitId)] -> MaybeErr UnitErr [UnitId]
closeUnitDeps' pkg_map current_ids ps = foldM (uncurry . add_unit pkg_map) current_ids ps

add_unit
  :: UnitInfoMap
  -> [UnitId]
  -> UnitId
  -> Maybe UnitId
  -> MaybeErr UnitErr [UnitId]
add_unit pkg_map ps p mb_parent
  | p `elem` ps = return ps
  | otherwise = case lookupUnitId' pkg_map p of
      Nothing -> Failed (CloseUnitErr p mb_parent)
      Just info -> do
        ps' <- foldM add_unit_key ps (unitDepends info)
        return (p:ps')
        where
          add_unit_key xs key
            = add_unit pkg_map xs key (Just p)

data UnitErr
  = CloseUnitErr !UnitId !(Maybe UnitId)
  | PackageFlagErr !PackageFlag ![(UnitInfo, UnusableUnitReason)]

mayThrowUnitErr :: MaybeErr UnitErr a -> IO a
mayThrowUnitErr = \case
  Failed e -> throwCsExceptionIO
              $ CmdLineError
              $ renderWithContext defaultSDocContext
              $ withPprStyle defaultUserStyle
              $ ppr e
  Succeeded a -> return a

instance Outputable UnitErr where
  ppr = \case
    CloseUnitErr p mb_parent
      -> (text "unknown unit:" <+> ppr p)
         <> case mb_parent of
              Nothing -> Outputable.empty
              Just parent -> space <> parens (text "dependency of"
                                              <+> ftext (unitIdFS parent))
    PackageFlagErr flag reasons
      -> flag_err (pprFlag flag) reasons
    where
      flag_err flag_doc reasons =
        text "cannot satisfy "
        <> flag_doc
        <> (if null reasons then Outputable.empty else text ": ")
        $$ nest 4 (vcat (map ppr_reason reasons)
                   $$ text "(use -v for more information)")

      ppr_reason (p, reason) = pprReason (ppr (unitId p) <+> text "is") reason

-- -----------------------------------------------------------------------------
-- Pretty-print a UnitId for the user.

pprUnitIdForUser :: UnitState -> UnitId -> SDoc
pprUnitIdForUser state uid@(UnitId fs) =
  case lookupUnitPprInfo state uid of
    Nothing -> ftext fs
    Just i -> ppr i

lookupUnitPprInfo :: UnitState -> UnitId -> Maybe UnitPprInfo
lookupUnitPprInfo state uid = fmap (mkUnitPprInfo unitIdFS) (lookupUnitId state uid)

-- -----------------------------------------------------------------------------
-- Displaying packages

pprUnits :: UnitState -> SDoc
pprUnits = pprUnitsWith pprUnitInfo

pprUnitsWith :: (UnitInfo -> SDoc) -> UnitState -> SDoc
pprUnitsWith pprIPI pkgstate =
  vcat (intersperse (text "---") (map pprIPI (listUnitInfo pkgstate)))

pprUnitsSimple :: UnitState -> SDoc
pprUnitsSimple = pprUnitsWith pprIPI
  where
    pprIPI ipi = let i = unitIdFS (unitId ipi)
                     e = if unitIsExposed ipi then text "E" else text " "
                 in e <> text "  " <> ftext i

pprModuleMap :: ModuleNameProvidersMap -> SDoc
pprModuleMap mod_map =
  vcat (map pprLine (nonDetUniqMapToList mod_map))
  where
    pprLine (m, e) = ppr m $$ nest 50 (vcat (map (pprEntry m) (nonDetUniqMapToList e)))
    pprEntry :: Outputable a => ModuleName -> (Module, a) -> SDoc
    pprEntry m (m', o)
      | m == moduleName m' = ppr (moduleUnit m') <+> parens (ppr o)
      | otherwise = ppr m' <+> parens (ppr o)

fsPackageName :: UnitInfo -> FastString
fsPackageName info = fs
  where
    PackageName fs = unitPackageName info

improveUnit' :: UnitInfoMap -> PreloadUnitClosure -> Unit -> Unit
improveUnit' _ _ uid@(RealUnit _) = uid
improveUnit' pkg_map closure uid =
  case lookupUnit' False pkg_map closure uid of
    Nothing -> uid
    Just pkg -> if unitId pkg `elementOfUniqSet` closure
                then mkUnit pkg
                else uid

type ShHoleSubst = ModuleNameEnv Module

renameHoleModule' :: UnitInfoMap -> PreloadUnitClosure -> ShHoleSubst -> Module -> Module
renameHoleModule' pkg_map closure env m
  | not (isHoleModule m)
  = let uid = renameHoleUnit' pkg_map closure env (moduleUnit m)
    in mkModule uid (moduleName m)
  | Just m' <- lookupUFM env (moduleName m) = m'
  | otherwise = m

renameHoleUnit' :: UnitInfoMap -> PreloadUnitClosure -> ShHoleSubst -> Unit -> Unit
renameHoleUnit' pkg_map closure env uid =
  case uid of
    (VirtUnit InstantiatedUnit { instUnitInstanceOf = cid
                               , instUnitInsts = insts
                               , instUnitHoles = fh })
      -> if isNullUFM (intersectUFM_C const (udfmToUfm (getUniqDSet fh)) env)
         then uid
         else improveUnit' pkg_map closure $
              mkVirtUnit cid
              (map (\(k, v) -> (k, renameHoleModule' pkg_map closure env v)) insts)
    _ -> uid

pprWithUnitState :: UnitState -> SDoc -> SDoc
pprWithUnitState state = updSDocContext (\ctx -> ctx
                                          { sdocUnitIdForUser =
                                              \fs -> pprUnitIdForUser state (UnitId fs) })
