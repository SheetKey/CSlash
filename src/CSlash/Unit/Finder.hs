{-# LANGUAGE MultiWayIf #-}

module CSlash.Unit.Finder
  ( FindResult(..)
  , InstalledFindResult(..)
  , FinderOpts(..)
  , FinderCache
  , initFinderCache
  , flushFinderCaches
  , findImportedModule
  , findExactModule
  , findHomeModule
  , findExposedPackageModule
  , mkHomeModLocation
  , mkHomeModLocation2
  , mkHiOnlyModLocation
  , mkHiPath
  , mkObjPath
  , addModuleToFinder
  , addHomeModuleToFinder

  , findObjectLinkable

  , lookupFinderCache
  ) where

import CSlash.Platform.Ways

import CSlash.Builtin.Names ( cSLASH_BUILTIN )

import CSlash.Unit.Env
import CSlash.Unit.Types
import CSlash.Unit.Module
import CSlash.Unit.Home
import CSlash.Unit.State
import CSlash.Unit.Finder.Types

import CSlash.Data.Maybe    ( expectJust )
import qualified GHC.Data.ShortText as ST

import CSlash.Utils.Misc
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic

import CSlash.Linker.Types
import CSlash.Types.PkgQual

import CSlash.Utils.Fingerprint
import Data.IORef
import System.Directory
import System.FilePath
import Control.Monad
import Data.Time
import qualified Data.Map as M
import CSlash.Driver.Env
    ( cs_home_unit_maybe, CsEnv(cs_FC, cs_dflags, cs_unit_env) )
import CSlash.Driver.Config.Finder
import qualified Data.Set as Set

type FileExt = String
type BaseName = String

-- -----------------------------------------------------------------------------
-- The finder's cache

initFinderCache :: IO FinderCache
initFinderCache = FinderCache <$> newIORef emptyInstalledModuleEnv
                              <*> newIORef M.empty

flushFinderCaches :: FinderCache -> UnitEnv -> IO ()
flushFinderCaches (FinderCache ref file_ref) ue = do
  atomicModifyIORef' ref $ \fm -> (filterInstalledModuleEnv is_ext fm, ())
  atomicModifyIORef' file_ref $ \_ -> (M.empty, ())
  where
    is_ext mod _ = not (isUnitEnvInstalledModule ue mod)

addToFinderCache :: FinderCache -> InstalledModule -> InstalledFindResult -> IO ()
addToFinderCache (FinderCache ref _) key val =
  atomicModifyIORef' ref $ \c -> (extendInstalledModuleEnv c key val, ())

lookupFinderCache :: FinderCache -> InstalledModule -> IO (Maybe InstalledFindResult)
lookupFinderCache (FinderCache ref _) key = do
  c <- readIORef ref
  return $! lookupInstalledModuleEnv c key

-- -----------------------------------------------------------------------------
-- The three external entry points

findImportedModule :: CsEnv -> ModuleName -> PkgQual -> IO FindResult
findImportedModule cs_env mod pkg_qual
  | otherwise
  = let fc = cs_FC cs_env
        mhome_unit = cs_home_unit_maybe cs_env
        dflags = cs_dflags cs_env
        fopts = initFinderOpts dflags
    in findImportedModuleNoCs fc fopts (cs_unit_env cs_env) mhome_unit mod pkg_qual

findImportedModuleNoCs
  :: FinderCache
  -> FinderOpts
  -> UnitEnv
  -> Maybe HomeUnit
  -> ModuleName
  -> PkgQual
  -> IO FindResult
findImportedModuleNoCs fc fopts ue mhome_unit mod_name mb_pkg =
  case mb_pkg of
    NoPkgQual -> unqual_import
    ThisPkg uid | (homeUnitId <$> mhome_unit) == Just uid -> home_import
                | Just os <- lookup uid other_fopts -> home_pkg_import (uid, os)
                | otherwise -> pprPanic "findImportModule" (ppr mod_name $$ ppr mb_pkg
                                                            $$ ppr (homeUnitId <$> mhome_unit)
                                                            $$ ppr uid $$ ppr (map fst all_opts))
    OtherPkg _ -> pkg_import
  where
    all_opts = case mhome_unit of
                 Nothing -> other_fopts
                 Just home_unit -> (homeUnitId home_unit, fopts) : other_fopts

    home_import = case mhome_unit of
                    Just home_unit -> findHomeModule fc fopts home_unit mod_name
                    Nothing -> pure $ NoPackage (panic "findImportedModule: no home-unit")

    home_pkg_import (uid, opts)
      | mod_name `Set.member` finder_reexportedModules opts
      = findImportedModuleNoCs fc opts ue (Just $ DefiniteHomeUnit uid Nothing) mod_name NoPkgQual
      | mod_name `Set.member` finder_hiddenModules opts
      = return (mkHomeHidden uid)
      | otherwise
      = findHomePackageModule fc opts uid mod_name

    any_home_import = foldr1 orIfNotFound (home_import : map home_pkg_import other_fopts)

    pkg_import = findExposedPackageModule fc fopts units mod_name mb_pkg

    unqual_import = any_home_import `orIfNotFound`
                    findExposedPackageModule fc fopts units mod_name NoPkgQual

    units = case mhome_unit of
              Nothing -> ue_units ue
              Just home_unit -> homeUnitEnv_units $ ue_findHomeUnitEnv (homeUnitId home_unit) ue

    hpt_deps :: [UnitId]
    hpt_deps = homeUnitDepends units

    other_fopts
      = map
        (\uid -> (uid, initFinderOpts (homeUnitEnv_dflags (ue_findHomeUnitEnv uid ue))))
        hpt_deps

findExactModule
  :: FinderCache
  -> FinderOpts
  -> UnitEnvGraph FinderOpts
  -> UnitState
  -> Maybe HomeUnit
  -> InstalledModule
  -> IO InstalledFindResult
findExactModule fc fopts other_fopts unit_state mhome_unit mod = 
  case mhome_unit of
    Just home_unit
      | isHomeInstalledModule home_unit mod
        -> findInstalledHomeModule fc fopts (homeUnitId home_unit) (moduleName mod)
      | Just home_fopts <- unitEnv_lookup_maybe (moduleUnit mod) other_fopts
        -> findInstalledHomeModule fc home_fopts (moduleUnit mod) (moduleName mod)
    _ -> findPackageModule fc unit_state fopts mod

-- -----------------------------------------------------------------------------
-- Helpers

orIfNotFound :: Monad m => m FindResult -> m FindResult -> m FindResult
orIfNotFound this or_this = do
  res <- this
  case res of
    NotFound { fr_paths = paths1, fr_mods_hidden = mh1, fr_pkgs_hidden = ph1
             , fr_unusables = u1, fr_suggestions = s1 }
      -> do res2 <- or_this
            case res2 of
              NotFound {fr_paths = paths2, fr_pkg = mb_pkg2, fr_mods_hidden = mh2
                       , fr_pkgs_hidden = ph2, fr_unusables = u2, fr_suggestions = s2 }
                -> return (NotFound { fr_paths = paths1 ++ paths2
                                    , fr_pkg = mb_pkg2
                                    , fr_mods_hidden = mh1 ++ mh2
                                    , fr_pkgs_hidden = ph1 ++ ph2
                                    , fr_unusables = u1 ++ u2
                                    , fr_suggestions = s1 ++ s2 })
              _ -> return res2
    _ -> return res

homeSearchCache
  :: FinderCache -> UnitId -> ModuleName -> IO InstalledFindResult -> IO InstalledFindResult
homeSearchCache fc home_unit mod_name do_this = 
  let mod = mkModule home_unit mod_name
  in modLocationCache fc mod do_this

findExposedPackageModule
  :: FinderCache -> FinderOpts -> UnitState -> ModuleName -> PkgQual -> IO FindResult
findExposedPackageModule fc fopts units mod_name mb_pkg =
  findLookupResult fc fopts
  $ lookupModuleWithSuggestions units mod_name mb_pkg

findLookupResult :: FinderCache -> FinderOpts -> LookupResult -> IO FindResult
findLookupResult fc fopts r = case r of
  LookupFound m pkg_conf -> do
    let im = fst (getModuleInstantiation m)
    r' <- findPackageModule_ fc fopts im (fst pkg_conf)
    case r' of
      InstalledFound loc _ -> return (Found loc m)
      InstalledNoPackage _ -> return (NoPackage (moduleUnit m))
      InstalledNotFound fp _ -> return (NotFound { fr_paths = fp
                                                 , fr_pkg = Just (moduleUnit m)
                                                 , fr_pkgs_hidden = []
                                                 , fr_mods_hidden = []
                                                 , fr_unusables = []
                                                 , fr_suggestions = [] })
  LookupMultiple rs -> return (FoundMultiple rs)
  LookupHidden pkg_hiddens mod_hiddens ->
    return (NotFound { fr_paths = []
                     , fr_pkg = Nothing
                     , fr_pkgs_hidden = map (moduleUnit . fst) pkg_hiddens
                     , fr_mods_hidden = map (moduleUnit . fst) mod_hiddens
                     , fr_unusables = []
                     , fr_suggestions = [] })
  LookupUnusable unusable ->
    let unusables' = map get_unusable unusable
        get_unusable (_, ModUnusable r) = r
        get_unusable (_, r) = pprPanic "findLookupResult: unexpected origin" (ppr r)
    in return (NotFound { fr_paths = []
                        , fr_pkg = Nothing
                        , fr_pkgs_hidden = []
                        , fr_mods_hidden = []
                        , fr_unusables = unusables'
                        , fr_suggestions = [] })
  LookupNotFound suggest ->
    let suggest' | finder_enableSuggestions fopts = suggest
                 | otherwise = []
    in return (NotFound { fr_paths = []
                        , fr_pkg = Nothing
                        , fr_pkgs_hidden = []
                        , fr_mods_hidden = []
                        , fr_unusables = []
                        , fr_suggestions = suggest' })

modLocationCache
  :: FinderCache -> InstalledModule -> IO InstalledFindResult -> IO InstalledFindResult
modLocationCache fc mod do_this = do
  m <- lookupFinderCache fc mod
  case m of
    Just result -> return result
    Nothing -> do
      result <- do_this
      addToFinderCache fc mod result
      return result

addModuleToFinder :: FinderCache -> Module -> ModLocation -> IO ()
addModuleToFinder fc mod loc = 
  let imod = toUnitId <$> mod
  in addToFinderCache fc imod (InstalledFound loc imod)

addHomeModuleToFinder :: FinderCache -> HomeUnit -> ModuleName -> ModLocation -> IO Module
addHomeModuleToFinder fc home_unit mod_name loc = do
  let mod = mkHomeInstalledModule home_unit mod_name
  addToFinderCache fc mod (InstalledFound loc mod)
  return (mkHomeModule home_unit mod_name)

-- -----------------------------------------------------------------------------
--      The internal workers

findHomeModule :: FinderCache -> FinderOpts -> HomeUnit -> ModuleName -> IO FindResult
findHomeModule fc fopts home_unit mod_name = do
  let uid = homeUnitAsUnit home_unit
  r <- findInstalledHomeModule fc fopts (homeUnitId home_unit) mod_name
  return $ case r of
    InstalledFound loc _ -> Found loc (mkHomeModule home_unit mod_name)
    InstalledNoPackage _ -> NoPackage uid
    InstalledNotFound fps _ -> NotFound
      { fr_paths = fps
      , fr_pkg = Just uid
      , fr_pkgs_hidden = []
      , fr_mods_hidden = []
      , fr_unusables = []
      , fr_suggestions = [] }

mkHomeHidden :: UnitId -> FindResult
mkHomeHidden uid = NotFound
  { fr_paths = []
  , fr_pkg = Just (RealUnit (Definite uid))
  , fr_mods_hidden = [RealUnit (Definite uid)]
  , fr_pkgs_hidden = []
  , fr_unusables = []
  , fr_suggestions = [] }

findHomePackageModule :: FinderCache -> FinderOpts -> UnitId -> ModuleName -> IO FindResult
findHomePackageModule fc fopts home_unit mod_name = do
  let uid = RealUnit (Definite home_unit)
  r <- findInstalledHomeModule fc fopts home_unit mod_name
  return $ case r of
    InstalledFound loc _ -> Found loc (mkModule uid mod_name)
    InstalledNoPackage _ -> NoPackage uid
    InstalledNotFound fps _ -> NotFound
      { fr_paths = fps
      , fr_pkg = Just uid
      , fr_pkgs_hidden = []
      , fr_mods_hidden = []
      , fr_unusables = []
      , fr_suggestions = [] }

findInstalledHomeModule
  :: FinderCache -> FinderOpts -> UnitId -> ModuleName -> IO InstalledFindResult
findInstalledHomeModule fc fopts home_unit mod_name = 
  let maybe_working_dir = finder_workingDirectory fopts
      home_path = case maybe_working_dir of
                    Nothing -> finder_importPaths fopts
                    Just fp -> augmentImports fp (finder_importPaths fopts)
      hi_dir_path = case finder_hiDir fopts of
                      Just hiDir -> case maybe_working_dir of
                                      Nothing -> [hiDir]
                                      Just fp -> [fp </> hiDir]
                      Nothing -> home_path
      hisuf = finder_hiSuf fopts
      mod = mkModule home_unit mod_name

      source_exts = [ ("csl", mkHomeModLocationSearched fopts mod_name "csl") ]

      hi_exts = [ (hisuf, mkHomeModHiOnlyLocation fopts mod_name) ]

      (search_dirs, exts)
        | finder_lookupHomeInterfaces fopts = (hi_dir_path, hi_exts)
        | otherwise = (home_path, source_exts)

  in homeSearchCache fc home_unit mod_name $
     if | mod `installedModuleEq` cSLASH_BUILTIN
          -> return (InstalledFound (error "CSL.BuiltIn ModLocation") mod)
        | otherwise
          -> searchPathExts search_dirs mod exts

augmentImports :: FilePath -> [FilePath] -> [FilePath]
augmentImports _ [] = []
augmentImports work_dir (fp:fps)
  | isAbsolute fp = fp : augmentImports work_dir fps
  | otherwise = (work_dir </> fp) : augmentImports work_dir fps

findPackageModule
  :: FinderCache -> UnitState -> FinderOpts -> InstalledModule -> IO InstalledFindResult
findPackageModule fc unit_state fopts mod =
  let pkg_id = moduleUnit mod
  in case lookupUnitId unit_state pkg_id of
    Nothing -> return (InstalledNoPackage pkg_id)
    Just u -> findPackageModule_ fc fopts mod u

findPackageModule_
  :: FinderCache -> FinderOpts -> InstalledModule -> UnitInfo -> IO InstalledFindResult
findPackageModule_ fc fopts mod pkg_conf = do
  massertPpr (moduleUnit mod == unitId pkg_conf)
             (ppr (moduleUnit mod) <+> ppr (unitId pkg_conf))
  modLocationCache fc mod $
    if | mod `installedModuleEq` cSLASH_BUILTIN
         -> return (InstalledFound (error "CSL.BuiltIn ModLocation") mod)
       | otherwise
         -> let tag = waysBuildTag (finder_ways fopts)
                package_hisuf | null tag = "hi"
                              | otherwise = tag ++ "_hi"
                package_dynhisuf = waysBuildTag (addWay WayDyn (finder_ways fopts)) ++ "_hi"
                mk_hi_loc = mkHiOnlyModLocation fopts package_hisuf package_dynhisuf
                import_dirs = map ST.unpack $ unitImportDirs pkg_conf
            in case import_dirs of
                 [one] | finder_bypassHiFileCheck fopts
                         -> let basename = moduleNameSlashes (moduleName mod)
                                loc = mk_hi_loc one basename
                            in return $ InstalledFound loc mod
                 _ -> searchPathExts import_dirs mod [(package_hisuf, mk_hi_loc)]

-- -----------------------------------------------------------------------------
-- General path searching

searchPathExts
  :: [FilePath]
  -> InstalledModule
  -> [(FileExt, FilePath -> BaseName -> ModLocation)]
  -> IO InstalledFindResult
searchPathExts paths mod exts = search to_search
  where
    basename = moduleNameSlashes (moduleName mod)

    to_search :: [(FilePath, ModLocation)]
    to_search = [ (file, fn path basename)
                | path <- paths
                , (ext, fn) <- exts
                , let base | path == "." = basename
                           | otherwise = path </> basename
                      file = base <.> ext
                ]

    search [] = return (InstalledNotFound (map fst to_search) (Just (moduleUnit mod)))
    search ((file, loc) : rest) = do
      b <- doesFileExist file
      if b
        then return $ InstalledFound loc mod
        else search rest
        
mkHomeModLocationSearched
  :: FinderOpts -> ModuleName -> FileExt -> FilePath -> BaseName -> ModLocation
mkHomeModLocationSearched fopts mod suff path basename
  = mkHomeModLocation2 fopts mod (path </> basename) suff

mkHomeModLocation :: FinderOpts -> ModuleName -> FilePath -> ModLocation
mkHomeModLocation dflags mod src_filename =
  let (basename, extension) = splitExtension src_filename
  in mkHomeModLocation2 dflags mod basename extension

mkHomeModLocation2 :: FinderOpts -> ModuleName -> FilePath -> String -> ModLocation
mkHomeModLocation2 fopts mod src_basename ext
  = let mod_basename = moduleNameSlashes mod

        obj_fn = mkObjPath fopts src_basename mod_basename
        dyn_obj_fn = mkDynObjPath fopts src_basename mod_basename
        hi_fn = mkHiPath fopts src_basename mod_basename
        dyn_hi_fn = mkDynHiPath fopts src_basename mod_basename
        hie_fn = mkHiePath fopts src_basename mod_basename

    in ModLocation { ml_cs_file = Just (src_basename <.> ext)
                   , ml_hi_file = hi_fn
                   , ml_dyn_hi_file = dyn_hi_fn
                   , ml_obj_file = obj_fn
                   , ml_dyn_obj_file = dyn_obj_fn
                   , ml_hie_file = hie_fn }

mkHomeModHiOnlyLocation :: FinderOpts -> ModuleName -> FilePath -> BaseName -> ModLocation
mkHomeModHiOnlyLocation fopts mod path basename =
  let loc = mkHomeModLocation2 fopts mod (path </> basename) ""
  in loc { ml_cs_file = Nothing }

mkHiOnlyModLocation :: FinderOpts -> Suffix -> Suffix -> FilePath -> String -> ModLocation
mkHiOnlyModLocation fopts hisuf dynhisuf path basename
  = let full_basename = path </> basename
        obj_fn = mkObjPath fopts full_basename basename
        dyn_obj_fn = mkDynObjPath fopts full_basename basename
        hie_fn = mkHiePath fopts full_basename basename
    in ModLocation { ml_cs_file = Nothing
                   , ml_hi_file = full_basename <.> hisuf
                   , ml_dyn_obj_file = dyn_obj_fn
                   , ml_dyn_hi_file = full_basename <.> dynhisuf
                   , ml_obj_file = obj_fn
                   , ml_hie_file = hie_fn
                   }

mkObjPath :: FinderOpts -> FilePath -> String -> FilePath
mkObjPath fopts basename mod_basename = obj_basename <.> osuf
  where
    odir = finder_objectDir fopts
    osuf = finder_objectSuf fopts
    obj_basename | Just dir <- odir = dir </> mod_basename
                 | otherwise = basename

mkDynObjPath :: FinderOpts -> FilePath -> String -> FilePath
mkDynObjPath fopts basename mod_basename = obj_basename <.> dynosuf
  where
    odir = finder_objectDir fopts
    dynosuf = finder_dynObjectSuf fopts
    obj_basename | Just dir <- odir = dir </> mod_basename
                 | otherwise = basename

mkHiPath :: FinderOpts -> FilePath -> String -> FilePath
mkHiPath fopts basename mod_basename = hi_basename <.> hisuf
  where
    hidir = finder_hiDir fopts
    hisuf = finder_hiSuf fopts
    hi_basename | Just dir <- hidir = dir </> mod_basename
                | otherwise = basename

mkDynHiPath :: FinderOpts -> FilePath -> String -> FilePath
mkDynHiPath fopts basename mod_basename = hi_basename <.> dynhisuf
  where
    hidir = finder_hiDir fopts
    dynhisuf = finder_dynHiSuf fopts
    hi_basename | Just dir <- hidir = dir </> mod_basename
                | otherwise = basename

mkHiePath :: FinderOpts -> FilePath -> String -> FilePath
mkHiePath fopts basename mod_basename = hie_basename <.> hiesuf
  where
    hiedir = finder_hieDir fopts
    hiesuf = finder_hieSuf fopts
    hie_basename | Just dir <- hiedir = dir </> mod_basename
                 | otherwise = basename

-- -----------------------------------------------------------------------------
-- findLinkable

findObjectLinkable :: Module -> FilePath -> UTCTime -> IO Linkable
findObjectLinkable mod obj_fn obj_time = return (LM obj_time mod [DotO obj_fn])
