module CSlash.Linker.Unit where

import CSlash.Platform.Ways
import CSlash.Unit.Types
import CSlash.Unit.Info
import CSlash.Unit.State
import CSlash.Unit.Env
import CSlash.Utils.Misc

import qualified GHC.Data.ShortText as ST

import CSlash.Settings

import Control.Monad
import System.Directory
import System.FilePath

getUnitLinkOpts
  :: CsNameVersion -> Ways -> UnitEnv -> [UnitId] -> IO ([String], [String], [String])
getUnitLinkOpts namever ways unit_env pkgs = do
  ps <- mayThrowUnitErr $ preloadUnitsInfo' unit_env pkgs
  return (collectLinkOpts namever ways ps)

collectLinkOpts :: CsNameVersion -> Ways -> [UnitInfo] -> ([String], [String], [String])
collectLinkOpts namever ways ps =
  ( concatMap (map ("-l" ++) . unitCsLibs namever ways) ps
  , concatMap (map ("-l" ++) . map ST.unpack . unitExtDepLibsSys) ps
  , concatMap (map ST.unpack . unitLinkerOptions) ps
  )

collectArchives :: CsNameVersion -> Ways -> UnitInfo -> IO [FilePath]
collectArchives namever ways pc =
  filterM doesFileExist [ searchPath </> ("lib" ++ lib ++ ".a")
                        | searchPath <- searchPaths
                        , lib <- libs ]
  where
    searchPaths = ordNub . filter notNull . libraryDirsForWay ways $ pc
    libs = unitCsLibs namever ways pc ++ map ST.unpack (unitExtDepLibsSys pc)

libraryDirsForWay :: Ways -> UnitInfo -> [String]
libraryDirsForWay ws
  | hasWay ws WayDyn = map ST.unpack . unitLibraryDynDirs
  | otherwise = map ST.unpack . unitLibraryDirs

getLibs :: CsNameVersion -> Ways -> UnitEnv -> [UnitId] -> IO [(String, String)]
getLibs namever ways unit_env pkgs = do
  ps <- mayThrowUnitErr $ preloadUnitsInfo' unit_env pkgs
  fmap concat . forM ps $ \p -> 
    let candidates = [ (l </> f, f) | l <- collectLibraryDirs ways [p]
                                    , f <- (\n -> "lib" ++ n ++ ".a")
                                           <$> unitCsLibs namever ways p ]
    in filterM (doesFileExist . fst) candidates
