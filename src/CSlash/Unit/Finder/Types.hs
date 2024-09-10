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

