module CSlash.Utils.TmpFs where

import CSlash.Utils.Error
import CSlash.Utils.Outputable
import CSlash.Utils.Logger
import CSlash.Utils.Misc
import CSlash.Utils.Exception as Exception
import CSlash.Driver.Phases

import Data.List (partition)
import qualified Data.Set as Set
import Data.Set (Set)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.IORef
import System.Directory
import System.FilePath
import System.IO.Error

data TmpFs = TmpFs
  { tmp_dirs_to_clean :: IORef (Map FilePath FilePath)
  , tmp_next_suffix :: IORef Int
  , tmp_files_to_clean :: IORef PathsToClean
  , tmp_subdirs_to_clean :: IORef PathsToClean
  }

data PathsToClean = PathsToClean
  { ptcCsSeccion :: !(Set FilePath)
  , ptcCurrentModule :: !(Set FilePath)
  }

data TempDir = TempDir FilePath
