module CSlash.Linker.Static
  ( linkBinary
  , linkStaticLib
  ) where

import CSlash.Platform
import CSlash.Platform.Ways
import CSlash.Settings

import CSlash.SysTools
-- import GHC.SysTools.Ar

import CSlash.Unit.Env
import CSlash.Unit.Types
import CSlash.Unit.Info
import CSlash.Unit.State

import CSlash.Utils.Logger
import CSlash.Utils.Monad
import CSlash.Utils.Misc
import CSlash.Utils.TmpFs

-- import GHC.Linker.MacOS
-- import GHC.Linker.Unit
-- import GHC.Linker.Dynamic
-- import GHC.Linker.ExtraObj
-- import GHC.Linker.External
-- import GHC.Linker.Windows
import CSlash.Linker.Static.Utils

-- import GHC.Driver.Config.Linker
import CSlash.Driver.Session

import System.FilePath
import System.Directory
import Control.Monad
import Data.Maybe

linkBinary :: Logger -> TmpFs -> DynFlags -> UnitEnv -> [FilePath] -> [UnitId] -> IO ()
linkBinary logger tmpfs dflags unit_env o_file dep_units = do error "linkBinary"
  -- let platform = ue_platform unit_env
  --     unit_state = ue_units unit_env
  --     toolSettings' = toolSettings dflags
  --     verbFlags = getVerbFlags dflags
  --     arch_os = platformArchOS platform
  --     output_fn = progFileName arch_os False (outputFile_ dflags)
  --     namever = csNameVersion dflags
  --     ways_ = ways dflags

  -- full_output_fn <- if isAbsolute output_fn
  --                   then return output_fn
  --                   else do d <- getCurrentDirectory
  --                           return $ normalise (d </> output_fn)

  -- pkgs <- mayThrowUnitErr (preloadUnitsInfo' unit_env dep_units)
  -- let pkg_lib_paths = collectLibraryDirs ways_ pkgs
  --     pkg_lib_path_opts' = concatMap get_pkg_lib_path_opts pkg_lib_paths
  --     get_pkg_lib_path_opts l
  --       | osElfTarget (platformOS platform)
  --         && dynLibLoader dflags == SystemDependent
  --         && ways_ `hasWay` WayDyn
  --       = let libpath = if gopt Opt_RelativeDynlibPaths dflags
  --                       then "$ORIGIN" </> (l `makeRelativeTo` full_output_fn)
  --                       else l
  --             rpath = if useXLinkerRPath dflags (platformOS platform)
  --                     then ["-Xlinker", "-rpath", "-Xlinker", libpath]
  --                     else []
  --             rpathlink = []
  --         in ["-L" ++ l] ++ rpath ++ rpathlink
  --       | otherwise = ["-L" ++ l]

  -- pkg_lib_path_opts <-
  --   if gopt Opt_SingleLibFolder dflags
  --   then do libs <- getLibs namever ways_ unit_env dep_units
  --           tmpDir <- newTempSubDir logger tmpfs (tmpDir dflags)
  --           sequence_ [ copyFile lib (tmpDir </> basename)
  --                     | (lib, basename) <- libs ]
  --           return ["-L" ++ tmpDir]
  --   else pure pkg_lib_path_opts'

  -- let lib_paths = libraryPaths dflags
  --     lib_path_opts = map ("-L" ++) lib_paths

  -- -- extraLinkObj <- maybeToList <$> mkExtraObjToLinkIntoBinary logger tmpfs dflags unit_state
  -- -- noteLinkObjs <- mkNoteObjsToLinkIntoBinary logger tmpfs dflags unit_env dep_units

  -- let (pre_cs_libs, post_cs_libs)
  --       | gopt Opt_WholeArchiveCsLibs dflags
  --       = (["-Wl,--whole-archive"], ["-Wl,--no-whole-archive"])
  --       | otherwise = ([], [])

  -- pkg_link_opts <- do
  --   (package_cs_libs, extra_libs, other_flags) <- getUnitLinkOpts namever ways_ unit_env dep_units
  --   return $ other_flags
  --            ++ dead_strip
  --            ++ pre_cs_libs
  --            ++ package_cs_libs
  --            ++ post_cs_libs
  --            ++ extra_libs

  -- let extra_ld_inputs = ldInputs dflags

  --     linker_config = initLinkerConfig dflags
  --     link dflags args = runLink logger tmpfs linker_config args
        
  -- link dflags ( map Option verbFlags
  --               ++ [ Option "-o"
  --                  , FileOption "" output_fn ]
  --               ++ libmLinkOpts platform
  --               ++ map Option
  --               ( pieCCLDOpts dflags
  --                 ++ (if toolSettings_ldIsGnuLd toolSettings'
  --                        && not (gopt Opt_WholeArchiveCsLibs dflags)
  --                      then ["-Wl,--gc-sections"]
  --                      else [])
  --                 ++ o_files
  --                 ++ lib_path_opts
  --               )
  --               ++ extra_ld_inputs
  --               ++ map Option
  --               ( pkg_lib_path_opts
  --                 -- ++ extraLinkObj
  --                 -- ++ noteLinkObjs
  --                 ++ pkg_link_opts
  --               )
  --             )

linkStaticLib :: Logger -> DynFlags -> UnitEnv -> [String] -> [UnitId] -> IO ()
linkStaticLib logger dflags unit_env o_files dep_units = do error "linkStaticLib"
  -- let platform = ue_platform unit_env
  --     extra_ld_unputs = [ f | FileOption _ f <- ldInputs dflags ]
  --     modules = o_files ++ extra_ld_inputs
  --     arch_os = platformArchOS platform
  --     output_fn = progFileName arch_os True (outputFile_ dflags)
  --     namever = csNameVersion dflags
  --     ways_ = ways dflags

  -- full_output_fn <- if isAbsolute output_fn
  --                   then return output_fn
  --                   else do d <- getCurrentDirectory
  --                           return $ normalise $ d </> output_fn

  -- output_exists <- doesFileExist full_output_fn
  -- (when output_exists) $ removeFile full_output_fn

  -- pkg_cfgs_init <- mayThrowUnitErr (preloadUnitsInfo' unit_env dep_units)

  -- let pkg_cfgs
  --       | gopt Opt_LinkRts dflags
  --       =  pkg_cfgs_init
  --       |otherwise
  --       = filter ((/= rtsUnitId) . unitId) pkg_cfgs_init

  -- archives <- concatMapM (collectArchives namever ways_) pkg_cfgs

  -- ar <- foldl mappend
  --       <$> (Archive <$> mapM loadObj modules)
  --       <*> mapM loadAr archives

  -- if toolSettings_ldIsGnuLd (toolSettings dflags)
  --   then writeGNUAr output_fn $ afilter (not . isGNUSymdef) ar
  --   else writeBSDAr output_fn $ afilter (not . isBSDSymdef) ar

  -- runRanlib logger dflags [FileOption "" output_fn]
