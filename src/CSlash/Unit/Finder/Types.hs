module CSlash.Unit.Finder.Types where

import CSlash.Unit
import qualified Data.Map as M
import CSlash.Utils.Fingerprint
import CSlash.Platform.Ways

import Data.IORef
import CSlash.Data.FastString
import qualified Data.Set as Set

type FinderCacheState = InstalledModuleEnv InstalledFindResult

type FileCacheState = M.Map FilePath Fingerprint

data FinderCache = FinderCache
  { fcModuleCache :: (IORef FinderCacheState)
  , fcFileCache :: (IORef FileCacheState)
  }

data InstalledFindResult
  = InstalledFound ModLocation InstalledModule
  | InstalledNoPackage UnitId
  | InstalledNotFound [FilePath] (Maybe UnitId)

data FindResult
  = Found ModLocation Module
  | NoPackage Unit
  | FoundMultiple [(Module, ModuleOrigin)]
  | NotFound
    { fr_paths :: [FilePath]
    , fr_pkg :: Maybe Unit
    , fr_mods_hidden :: [Unit]
    , fr_pkgs_hidden :: [Unit]
    , fr_unusables :: [UnusableUnit]
    , fr_suggestions :: [ModuleSuggestion]
    }

data FinderOpts = FinderOpts
  { finder_importPaths :: [FilePath]
  , finder_lookupHomeInterfaces :: Bool
  , finder_bypassHiFileCheck :: Bool
  , finder_ways :: Ways
  , finder_enableSuggestions :: Bool
  , finder_workingDirectory :: Maybe FilePath
  , finder_thisPackageName :: Maybe FastString
  , finder_hiddenModules :: Set.Set ModuleName
  , finder_reexportedModules :: Set.Set ModuleName
  , finder_hieDir :: Maybe FilePath
  , finder_hieSuf :: String
  , finder_hiDir :: Maybe FilePath
  , finder_hiSuf :: String
  , finder_dynHiSuf :: String
  , finder_objectDir :: Maybe FilePath
  , finder_objectSuf :: String
  , finder_dynObjectSuf :: String
  , finder_stubDir :: Maybe FilePath
  }
  deriving Show
