module CSlash.Utils.TmpFs where

import Prelude hiding ((<>))

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
  { ptcCsSession :: !(Set FilePath)
  , ptcCurrentModule :: !(Set FilePath)
  }

newtype TempDir = TempDir FilePath

emptyPathsToClean :: PathsToClean
emptyPathsToClean = PathsToClean Set.empty Set.empty

initTmpFs :: IO TmpFs
initTmpFs = do
  files <- newIORef emptyPathsToClean
  subdirs <- newIORef emptyPathsToClean
  dirs <- newIORef Map.empty
  next <- newIORef 0
  return $ TmpFs
    { tmp_files_to_clean = files
    , tmp_subdirs_to_clean = subdirs
    , tmp_dirs_to_clean = dirs
    , tmp_next_suffix = next
    }

cleanTempDirs :: Logger -> TmpFs -> IO ()
cleanTempDirs logger tmpfs = mask_ $ do
  let ref = tmp_dirs_to_clean tmpfs
  ds <- atomicModifyIORef' ref $ \ds -> (Map.empty, ds)
  removeTmpDirs logger (Map.elems ds)

cleanTempFiles :: Logger -> TmpFs -> IO ()
cleanTempFiles logger tmpfs = mask_ $ do
  removeWith (removeTmpFiles logger) (tmp_files_to_clean tmpfs)
  removeWith (removeTmpSubdirs logger) (tmp_subdirs_to_clean tmpfs)
  where
    removeWith remove ref = do
      to_delete <- atomicModifyIORef' ref $
        \PathsToClean { ptcCurrentModule = cm_paths
                      , ptcCsSession = cs_paths
                      } -> ( emptyPathsToClean
                           , Set.toList cm_paths ++ Set.toList cs_paths)
      remove to_delete

removeTmpDirs :: Logger -> [FilePath] -> IO ()
removeTmpDirs logger ds
  = traceCmd logger "Deleting temp dirs"
             ("Deleting: " ++ unwords ds)
             (mapM_ (removeWith logger removeDirectory) ds)

removeTmpFiles :: Logger -> [FilePath] -> IO ()
removeTmpFiles logger fs
  = warnNon $
    traceCmd logger "Deleting temp files"
             ("Deleting: " ++ unwords deletees)
             (mapM_ (removeWith logger removeFile) deletees)

  where
    warnNon act
      | null non_deletees = act
      | otherwise = do
          putMsg logger (text "WARNING - NOT deleting source files:"
                         <+> hsep (map text non_deletees))
          act
    (non_deletees, deletees) = partition isCsUserSrcFilename fs

removeTmpSubdirs :: Logger -> [FilePath] -> IO ()
removeTmpSubdirs logger fs
  = traceCmd logger "Deleting temp subdirs"
             ("Deleting: " ++ unwords fs)
             (mapM_ (removeWith logger removeDirectory) fs)

removeWith :: Logger -> (FilePath -> IO ()) -> FilePath -> IO ()
removeWith logger remover f = remover f `Exception.catchIO`
  (\ e ->
     let msg = if isDoesNotExistError e
               then text "Warning: deleting non-existent" <+> text f
               else text "Warning: exception raised when deleting"
                    <+> text f <> colon
                    $$ text (show e)
     in debugTraceMsg logger 2 msg
  ) 
