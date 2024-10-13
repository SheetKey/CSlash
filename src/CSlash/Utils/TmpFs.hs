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

import qualified System.Posix.Internals

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

data TempFileLifetime
  = TFL_CurrentModule
  | TFL_CslSession
  deriving (Show)

newtype TempDir = TempDir FilePath

emptyPathsToClean :: PathsToClean
emptyPathsToClean = PathsToClean Set.empty Set.empty

mergePathsToClean :: PathsToClean -> PathsToClean -> PathsToClean
mergePathsToClean x y = PathsToClean
  { ptcCsSession = Set.union (ptcCsSession x) (ptcCsSession y)
  , ptcCurrentModule = Set.union (ptcCurrentModule x) (ptcCurrentModule y)
  }

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

forkTmpFsFrom :: TmpFs -> IO TmpFs
forkTmpFsFrom old = do
  files <- newIORef emptyPathsToClean
  subdirs <- newIORef emptyPathsToClean
  return $ TmpFs
    { tmp_files_to_clean = files
    , tmp_subdirs_to_clean = subdirs
    , tmp_dirs_to_clean = tmp_dirs_to_clean old
    , tmp_next_suffix = tmp_next_suffix old
    }

mergeTmpFsInto :: TmpFs -> TmpFs -> IO ()
mergeTmpFsInto src dst = do
  src_files <- atomicModifyIORef' (tmp_files_to_clean src) (\s -> (emptyPathsToClean, s))
  src_subdirs <- atomicModifyIORef' (tmp_subdirs_to_clean src) (\s -> (emptyPathsToClean, s))
  atomicModifyIORef' (tmp_files_to_clean dst) (\s -> (mergePathsToClean src_files s, ()))
  atomicModifyIORef' (tmp_subdirs_to_clean dst) (\s -> (mergePathsToClean src_subdirs s, ()))

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

keepCurrentModuleTempFiles :: HasCallStack => Logger -> TmpFs -> IO ()
keepCurrentModuleTempFiles logger tmpfs = mask_ $ do
  to_keep_files <- keep (tmp_files_to_clean tmpfs)
  to_keep_subdirs <- keep (tmp_subdirs_to_clean tmpfs)
  keepDirs (to_keep_files ++ to_keep_subdirs) (tmp_dirs_to_clean tmpfs)
  where
    keepDirs keeps ref = 
      let keep_dirs = Set.fromList (map takeDirectory keeps)
      in atomicModifyIORef' ref $ \m -> (Map.filter (\fp -> fp `Set.notMember` keep_dirs) m, ())
    keep ref = do
      to_keep <- atomicModifyIORef' ref $
        \ptc@PathsToClean{ ptcCurrentModule = cm_paths } ->
          (ptc{ ptcCurrentModule = Set.empty }, Set.toList cm_paths)
      debugTraceMsg logger 2 (text "Keeping:" <+> hsep (map text to_keep))
      return to_keep

cleanCurrentModuleTempFiles :: Logger -> TmpFs -> IO ()
cleanCurrentModuleTempFiles logger tmpfs = mask_ $ do
  removeWith (removeTmpFiles logger) (tmp_files_to_clean tmpfs)
  removeWith (removeTmpSubdirs logger) (tmp_subdirs_to_clean tmpfs)
  where
    removeWith remove ref = do
      to_delete <- atomicModifyIORef' ref $
        \ptc@PathsToClean{ ptcCurrentModule = cm_paths } ->
          (ptc{ ptcCurrentModule = Set.empty }, Set.toList cm_paths)
      remove to_delete
  

addFilesToClean :: TmpFs -> TempFileLifetime -> [FilePath] -> IO ()
addFilesToClean tmpfs lifetime new_files =
  addToClean (tmp_files_to_clean tmpfs) lifetime new_files

addSubdirsToClean :: TmpFs -> TempFileLifetime -> [FilePath] -> IO ()
addSubdirsToClean tmpfs lifetime new_subdirs =
  addToClean (tmp_subdirs_to_clean tmpfs) lifetime new_subdirs

addToClean :: IORef PathsToClean -> TempFileLifetime -> [FilePath] -> IO ()
addToClean ref lifetime new_filepaths = modifyIORef' ref $
  \PathsToClean { ptcCurrentModule = cm_paths, ptcCsSession = cs_paths }
  -> case lifetime of
       TFL_CurrentModule -> PathsToClean
         { ptcCurrentModule = cm_paths `Set.union` new_filepaths_set
         , ptcCsSession = cs_paths `Set.difference` new_filepaths_set
         }
       TFL_CslSession -> PathsToClean
         { ptcCurrentModule = cm_paths `Set.difference` new_filepaths_set
         , ptcCsSession = cs_paths `Set.union` new_filepaths_set
         }
  where
    new_filepaths_set = Set.fromList new_filepaths

newTempSuffix :: TmpFs -> IO Int
newTempSuffix tmpfs = atomicModifyIORef' (tmp_next_suffix tmpfs) $ \n -> (n+1, n)

newTempName :: Logger -> TmpFs -> TempDir -> TempFileLifetime -> Suffix -> IO FilePath
newTempName logger tmpfs tmp_dir lifetime extn = do
    d <- getTempDir logger tmpfs tmp_dir
    findTempName (d </> "csl_")
  where
    findTempName :: FilePath -> IO FilePath
    findTempName prefix = do
      n <- newTempSuffix tmpfs
      let filename = prefix ++ show n <.> extn
      b <- doesFileExist filename
      if b
        then findTempName prefix
        else do addFilesToClean tmpfs lifetime [filename]
                return filename

newTempSubDir :: Logger -> TmpFs -> TempDir -> IO FilePath
newTempSubDir logger tmpfs tmp_dir = do
  d <- getTempDir logger tmpfs tmp_dir
  findTempDir (d </> "csl_")
  where
    findTempDir :: FilePath -> IO FilePath
    findTempDir prefix = do
      n <- newTempSuffix tmpfs
      let name = prefix ++ show n
      b <- doesDirectoryExist name
      if b then findTempDir prefix
        else (flip Exception.catchIO)
             (\e -> if isAlreadyExistsError e
                    then findTempDir prefix else ioError e)
             $ do createDirectory name
                  addSubdirsToClean tmpfs TFL_CslSession [name]
                  return name
        

getTempDir :: Logger -> TmpFs -> TempDir -> IO FilePath
getTempDir logger tmpfs (TempDir tmp_dir) = do
  mapping <- readIORef dir_ref
  case Map.lookup tmp_dir mapping of
    Nothing -> do
      pid <- getProcessID
      let prefix = tmp_dir </> "csl" ++ show pid ++ "_"
      mask_ $ mkTempDir prefix
    Just dir -> return dir
  where
    dir_ref = tmp_dirs_to_clean tmpfs

    mkTempDir :: FilePath -> IO FilePath
    mkTempDir prefix = (flip Exception.catchIO)
      (\e -> if isAlreadyExistsError e then mkTempDir prefix else ioError e) $ do
      n <- newTempSuffix tmpfs
      let our_dir = prefix ++ show n

      createDirectory our_dir

      their_dir <- atomicModifyIORef' dir_ref $ \mapping ->
        case Map.lookup tmp_dir mapping of
          Just dir -> (mapping, Just dir)
          Nothing -> (Map.insert tmp_dir our_dir mapping, Nothing)

      case their_dir of
        Nothing -> do
          debugTraceMsg logger 2 $
            text "Created temporary directory:" <+> text our_dir
          return our_dir
        Just dir -> do
          removeDirectory our_dir
          return dir

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

getProcessID :: IO Int
getProcessID = System.Posix.Internals.c_getpid >>= return . fromIntegral
