module CSlash.Unit.Finder where

import CSlash.Platform.Ways

import CSlash.Builtin.Names ( cSLASH_PRIM )

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

-- import GHC.Linker.Types
import CSlash.Types.PkgQual

import CSlash.Utils.Fingerprint
import Data.IORef
import System.Directory
import System.FilePath
import Control.Monad
import Data.Time
import qualified Data.Map as M
import CSlash.Driver.Env
    ( {-cs_home_unit_maybe,-} CsEnv(cs_FC, cs_dflags, cs_unit_env) )
-- import GHC.Driver.Config.Finder
import qualified Data.Set as Set

type FileExt = String
type BaseName = String

-- -----------------------------------------------------------------------------
-- The finder's cache

initFinderCache :: IO FinderCache
initFinderCache = FinderCache <$> newIORef emptyInstalledModuleEnv
                              <*> newIORef M.empty
