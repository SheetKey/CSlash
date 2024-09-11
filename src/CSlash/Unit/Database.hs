{-# LANGUAGE RecordWildCards #-}

module CSlash.Unit.Database 
  ( GenericUnitInfo(..)
  , type DbUnitInfo
  , DbModule (..)
  , DbInstUnitId (..)
  , mapGenericUnitInfo

  , DbMode(..)
  , DbOpenMode(..)
  , isDbOpenReadMode
  , readPackageDbForCs
  , readPackageDbForCsPkg
  , writePackageDb

  , PackageDbLock
  , lockPackageDb
  , unlockPackageDb

  , mkMungePathUrl
  , mungeUnitInfoPaths
  ) where

import Data.Version (Version(..))
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BS.Char8
import qualified Data.ByteString.Lazy as BS.Lazy
import qualified Data.ByteString.Lazy.Internal as BS.Lazy (defaultChunkSize)
import qualified Data.Foldable as F
import qualified Data.Traversable as F
import Data.Bifunctor
import Data.Binary as Bin
import Data.Binary.Put as Bin
import Data.Binary.Get as Bin
import Data.List (intersperse)
import Control.Exception as Exception
import Control.Monad (when)
import System.FilePath as FilePath
import System.IO
import System.IO.Error
import GHC.IO.Exception (IOErrorType(InappropriateType))
import qualified GHC.Data.ShortText as ST
import GHC.IO.Handle.Lock
import System.Directory

type DbUnitInfo = GenericUnitInfo BS.ByteString BS.ByteString BS.ByteString BS.ByteString DbModule

data GenericUnitInfo srcpkgid srcpkgname uid modulename mod = GenericUnitInfo
   { unitId             :: uid
   , unitInstanceOf     :: uid
   , unitInstantiations :: [(modulename, mod)]
   , unitPackageId      :: srcpkgid
   , unitPackageName    :: srcpkgname
   , unitPackageVersion :: Version
   , unitAbiHash        :: ST.ShortText
   , unitDepends        :: [uid]
   , unitAbiDepends     :: [(uid, ST.ShortText)]
   , unitImportDirs     :: [FilePathST]
   , unitLibraries      :: [ST.ShortText]
   , unitExtDepLibsSys  :: [ST.ShortText]
   , unitLibraryDirs    :: [FilePathST]
   , unitLibraryDynDirs :: [FilePathST]
   , unitLinkerOptions  :: [ST.ShortText]
   , unitIncludes       :: [ST.ShortText]
   , unitIncludeDirs    :: [FilePathST]
   , unitExposedModules :: [(modulename, Maybe mod)]
   , unitHiddenModules  :: [modulename]
   , unitIsIndefinite   :: Bool
   , unitIsExposed      :: Bool
   }
   deriving (Eq, Show)

type FilePathST = ST.ShortText

mapGenericUnitInfo
   :: (uid1 -> uid2)
   -> (srcpkg1 -> srcpkg2)
   -> (srcpkgname1 -> srcpkgname2)
   -> (modname1 -> modname2)
   -> (mod1 -> mod2)
   -> (GenericUnitInfo srcpkg1 srcpkgname1 uid1 modname1 mod1
       -> GenericUnitInfo srcpkg2 srcpkgname2 uid2 modname2 mod2)
mapGenericUnitInfo fuid fsrcpkg fsrcpkgname fmodname fmod g@(GenericUnitInfo {..}) =
   g { unitId              = fuid unitId
     , unitInstanceOf      = fuid unitInstanceOf
     , unitInstantiations  = fmap (bimap fmodname fmod) unitInstantiations
     , unitPackageId       = fsrcpkg unitPackageId
     , unitPackageName     = fsrcpkgname unitPackageName
     , unitComponentName   = fmap fsrcpkgname unitComponentName
     , unitDepends         = fmap fuid unitDepends
     , unitAbiDepends      = fmap (first fuid) unitAbiDepends
     , unitExposedModules  = fmap (bimap fmodname (fmap fmod)) unitExposedModules
     , unitHiddenModules   = fmap fmodname unitHiddenModules
     }

data DbModule
   = DbModule
      { dbModuleUnitId  :: DbInstUnitId
      , dbModuleName    :: BS.ByteString
      }
   | DbModuleVar
      { dbModuleVarName :: BS.ByteString
      }
   deriving (Eq, Show)

data DbInstUnitId
   = DbInstUnitId
      BS.ByteString               -- component id
      [(BS.ByteString, DbModule)] -- instantiations: [(modulename,module)]

   | DbUnitId
      BS.ByteString               -- unit id
  deriving (Eq, Show)

newtype PackageDbLock = PackageDbLock Handle

lockPackageDb :: FilePath -> IO PackageDbLock

unlockPackageDb :: PackageDbLock -> IO ()

lockPackageDbWith :: LockMode -> FilePath -> IO PackageDbLock
lockPackageDbWith mode file = do
  catchJust
    (\e -> if isPermissionError e then Just () else Nothing)
    (lockFileOpenIn ReadWriteMode)
    (const $ lockFileOpenIn ReadMode)
  where
    lock = file <.> "lock"

    lockFileOpenIn io_mode = bracketOnError
      (openBinaryFile lock io_mode)
      hClose
      $ \hnd -> do hLock hnd mode `catch` \FileLockingNotSupported -> return ()
                   return $ PackageDbLock hnd

lockPackageDb = lockPackageDbWith ExclusiveLock
unlockPackageDb (PackageDbLock hnd) = do
    hUnlock hnd
    hClose hnd

data DbMode = DbReadOnly | DbReadWrite

data DbOpenMode (mode :: DbMode) t where
  DbOpenReadOnly  ::      DbOpenMode 'DbReadOnly t
  DbOpenReadWrite :: t -> DbOpenMode 'DbReadWrite t

deriving instance Functor (DbOpenMode mode)
deriving instance F.Foldable (DbOpenMode mode)
deriving instance F.Traversable (DbOpenMode mode)

isDbOpenReadMode :: DbOpenMode mode t -> Bool
isDbOpenReadMode = \case
  DbOpenReadOnly    -> True
  DbOpenReadWrite{} -> False

readPackageDbForCs :: FilePath -> IO [DbUnitInfo]
readPackageDbForCs file =
  decodeFromFile file DbOpenReadOnly getDbForCs >>= \case
    (pkgs, DbOpenReadOnly) -> return pkgs
  where
    getDbForCs = do
      _version    <- getHeader
      _csPartLen <- get :: Get Word32
      csPart     <- get
      return csPart

readPackageDbForCsPkg :: Binary pkgs => FilePath -> DbOpenMode mode t ->
                          IO (pkgs, DbOpenMode mode PackageDbLock)
readPackageDbForCsPkg file mode =
    decodeFromFile file mode getDbForCsPkg
  where
    getDbForCsPkg = do
      _version    <- getHeader
      csPartLen  <- get :: Get Word32
      _csPart    <- skip (fromIntegral csPartLen)
      csPkgPart  <- get
      return csPkgPart

writePackageDb :: Binary pkgs => FilePath -> [DbUnitInfo] -> pkgs -> IO ()
writePackageDb file csPkgs csPkgPart = do
  writeFileAtomic file (runPut putDbForcsPkg)
  return ()
  where
    putDbForCsPkg = do
        putHeader
        put               csPartLen
        putLazyByteString csPart
        put               csPkgPart
      where
        csPartLen :: Word32
        csPartLen = fromIntegral (BS.Lazy.length csPart)
        csPart    = encode csPkgs

getHeader :: Get (Word32, Word32)
getHeader = do
    magic <- getByteString (BS.length headerMagic)
    when (magic /= headerMagic) $
      fail "not a cs-pkg db file, wrong file magic number"

    majorVersion <- get :: Get Word32

    minorVersion <- get :: Get Word32

    when (majorVersion /= 1) $
      fail "unsupported cs-pkg db format version"

    headerExtraLen <- get :: Get Word32
    skip (fromIntegral headerExtraLen)

    return (majorVersion, minorVersion)

putHeader :: Put
putHeader = do
    putByteString headerMagic
    put majorVersion
    put minorVersion
    put headerExtraLen
  where
    majorVersion   = 1 :: Word32
    minorVersion   = 0 :: Word32
    headerExtraLen = 0 :: Word32

headerMagic :: BS.ByteString
headerMagic = BS.Char8.pack "\0cspkg\0"


decodeFromFile :: FilePath -> DbOpenMode mode t -> Get pkgs ->
                  IO (pkgs, DbOpenMode mode PackageDbLock)
decodeFromFile file mode decoder = case mode of
  DbOpenReadOnly -> do
      (, DbOpenReadOnly) <$> decodeFileContents
  DbOpenReadWrite{} -> do
    bracketOnError (lockPackageDb file) unlockPackageDb $ \lock -> do
      (, DbOpenReadWrite lock) <$> decodeFileContents
  where
    decodeFileContents = withBinaryFile file ReadMode $ \hnd ->
      feed hnd (runGetIncremental decoder)

    feed hnd (Partial k)  = do chunk <- BS.hGet hnd BS.Lazy.defaultChunkSize
                               if BS.null chunk
                                 then feed hnd (k Nothing)
                                 else feed hnd (k (Just chunk))
    feed _ (Done _ _ res) = return res
    feed _ (Fail _ _ msg) = ioError err
      where
        err = mkIOError InappropriateType loc Nothing (Just file)
              `ioeSetErrorString` msg
        loc = "CSlash.Unit.Database.readPackageDb"

writeFileAtomic :: FilePath -> BS.Lazy.ByteString -> IO ()
writeFileAtomic targetPath content = do
  let (targetDir, targetFile) = splitFileName targetPath
  Exception.bracketOnError
    (openBinaryTempFileWithDefaultPermissions targetDir $ targetFile <.> "tmp")
    (\(tmpPath, handle) -> hClose handle >> removeFile tmpPath)
    (\(tmpPath, handle) -> do
        BS.Lazy.hPut handle content
        hClose handle
        renameFile tmpPath targetPath)

instance Binary DbUnitInfo where
  put (GenericUnitInfo {..}) = do
    put unitPackageId
    put unitPackageName
    put unitPackageVersion
    put unitId
    put unitInstanceOf
    put unitInstantiations
    put unitAbiHash
    put unitDepends
    put unitAbiDepends
    put unitImportDirs
    put unitLibraries
    put unitExtDepLibsSys
    put unitLibraryDirs
    put unitLibraryDynDirs
    put unitLinkerOptions
    put unitIncludes
    put unitIncludeDirs
    put unitExposedModules
    put unitHiddenModules
    put unitIsIndefinite
    put unitIsExposed

  get = do
    unitPackageId      <- get
    unitPackageName    <- get
    unitPackageVersion <- get
    unitId             <- get
    unitInstanceOf     <- get
    unitInstantiations <- get
    unitAbiHash        <- get
    unitDepends        <- get
    unitAbiDepends     <- get
    unitImportDirs     <- get
    unitLibraries      <- get
    unitExtDepLibsSys  <- get
    unitLibraryDirs    <- get
    unitLibraryDynDirs <- get
    unitLinkerOptions  <- get
    unitIncludes       <- get
    unitIncludeDirs    <- get
    unitExposedModules <- get
    unitHiddenModules  <- get
    unitIsIndefinite   <- get
    unitIsExposed      <- get
    return (GenericUnitInfo {..})

instance Binary DbModule where
  put (DbModule dbModuleUnitId dbModuleName) = do
    putWord8 0
    put dbModuleUnitId
    put dbModuleName
  put (DbModuleVar dbModuleVarName) = do
    putWord8 1
    put dbModuleVarName
  get = do
    b <- getWord8
    case b of
      0 -> DbModule <$> get <*> get
      _ -> DbModuleVar <$> get

instance Binary DbInstUnitId where
  put (DbUnitId uid) = do
    putWord8 0
    put uid
  put (DbInstUnitId dbUnitIdComponentId dbUnitIdInsts) = do
    putWord8 1
    put dbUnitIdComponentId
    put dbUnitIdInsts

  get = do
    b <- getWord8
    case b of
      0 -> DbUnitId <$> get
      _ -> DbInstUnitId <$> get <*> get


mkMungePathUrl :: FilePathST -> FilePathST -> (FilePathST -> FilePathST, FilePathST -> FilePathST)
mkMungePathUrl top_dir pkgroot = (munge_path, munge_url)
   where
    munge_path p
      | Just p' <- stripVarPrefix "${pkgroot}" p = mappend pkgroot p'
      | Just p' <- stripVarPrefix "$topdir"    p = mappend top_dir p'
      | otherwise                                = p

    munge_url p
      | Just p' <- stripVarPrefix "${pkgrooturl}" p = toUrlPath pkgroot p'
      | Just p' <- stripVarPrefix "$httptopdir"   p = toUrlPath top_dir p'
      | otherwise                                   = p

    toUrlPath r p = mconcat $ "file:///" : (intersperse "/" (r : (splitDirectories p)))

    splitDirectories :: FilePathST -> [FilePathST]
    splitDirectories p  = filter (not . ST.null) $ ST.splitFilePath p

    stripVarPrefix var path = case ST.stripPrefix var path of
                              Just "" -> Just ""
                              Just cs | isPathSeparator (ST.head cs) -> Just cs
                              _ -> Nothing

mungeUnitInfoPaths
  :: FilePathST -> FilePathST -> GenericUnitInfo a b c d e -> GenericUnitInfo a b c d e
mungeUnitInfoPaths top_dir pkgroot pkg =
    pkg
      { unitImportDirs          = munge_paths (unitImportDirs pkg)
      , unitIncludeDirs         = munge_paths (unitIncludeDirs pkg)
      , unitLibraryDirs         = munge_paths (unitLibraryDirs pkg)
      , unitLibraryDynDirs      = munge_paths (unitLibraryDynDirs pkg)
      }
   where
      munge_paths = map munge_path
      munge_urls  = map munge_url
      (munge_path,munge_url) = mkMungePathUrl top_dir pkgroot
