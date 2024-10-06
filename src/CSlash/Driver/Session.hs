{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE DeriveFunctor #-}

module CSlash.Driver.Session
  ( DumpFlag(..)
  , GeneralFlag(..)
  , WarningFlag(..)
  , FatalMessager, FlushOut(..)
  , hasPprDebug, hasNoDebugOutput, hasNoStateHack
  , dopt
  , gopt
  , wopt
  , DynFlags(..)
  , outputFile
  , HasDynFlags(..), ContainsDynFlags(..)
  , CsMode(..), isOneShot
  , CsLink(..), isNoLink
  , Option(..), showOpt
  , makeDynFlagsConsistent
  , setFlagsFromEnvFile

  , Settings(..)
  , programName, projectVersion
  , csUsagePath
  , versionedAppDir, versionedFilePath
  , updatePlatformConstants

  , defaultDynFlags
  , initDynFlags
  , defaultFatalMessager
  , defaultFlushOut
  , augmentByWorkingDirectory

  , CmdLineP(..), runCmdLineP
  , getCmdLineState, putCmdLineState
  , processCmdLineP

  , parseDynamicFlagsCmdLine
  , parseDynamicFlagsFull

  , flagsForCompletion

  , compilerInfo

  , setUnsafeGlobalDynFlags
  ) where 

import CSlash.Platform
import CSlash.Platform.Ways
-- import CSlash.Platform.Profile

import CSlash.Unit.Types
import CSlash.Unit.Parser
import CSlash.Unit.Module
import CSlash.Unit.Module.Warnings
import CSlash.Driver.DynFlags
import CSlash.Driver.Config.Diagnostic
import CSlash.Driver.Flags
import CSlash.Driver.Backend
import CSlash.Driver.Errors.Types
-- import GHC.Driver.Plugins.External
import CSlash.Settings.Config
import CSlash.Core.Unfold
import CSlash.Driver.CmdLine
import CSlash.Utils.Panic
import CSlash.Utils.Misc
import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.GlobalVars
import CSlash.Data.Maybe
import CSlash.Data.Bool
import CSlash.Types.Error
import CSlash.Utils.Monad
import CSlash.Types.SrcLoc
-- import GHC.Types.SafeHaskell
import CSlash.Types.Basic ( treatZeroAsInf )
import CSlash.Data.FastString
import CSlash.Utils.TmpFs
import CSlash.Utils.Fingerprint
import CSlash.Utils.Outputable
import CSlash.Settings
-- import GHC.CmmToAsm.CFG.Weight
import CSlash.Core.Opt.CallerCC

import CSlash.SysTools.BaseDir ( expandToolDir, expandTopDir )

import Data.IORef
import Control.Arrow ((&&&))
import Control.Monad
import Control.Monad.Trans.State as State
import Data.Functor.Identity

import Data.Ord
import Data.Char
import Data.List (intercalate, sortBy, partition)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Word
import System.FilePath
import Text.ParserCombinators.ReadP hiding (char)
import Text.ParserCombinators.ReadP as R

import qualified GHC.Data.EnumSet as EnumSet

-- import qualified GHC.LanguageExtensions as LangExt

setObjectDir :: String -> DynFlags -> DynFlags
setObjectDir f d = d { objectDir = Just f }

setHiDir :: String -> DynFlags -> DynFlags
setHiDir f d = d { hiDir      = Just f}

setHieDir :: String -> DynFlags -> DynFlags
setHieDir f d = d { hieDir     = Just f}

setStubDir :: String -> DynFlags -> DynFlags
setStubDir f d = d { stubDir    = Just f
                   , includePaths = addGlobalInclude (includePaths d) [f] }

setDumpDir :: String -> DynFlags -> DynFlags
setDumpDir f d = d { dumpDir    = Just f}

setOutputDir :: String -> DynFlags -> DynFlags
setOutputDir f = setObjectDir f
                 . setHieDir f
                 . setHiDir f
                 . setStubDir f
                 . setDumpDir f

setObjectSuf :: String -> DynFlags -> DynFlags
setObjectSuf f d = d { objectSuf_    = f}

setDynObjectSuf :: String -> DynFlags -> DynFlags
setDynObjectSuf f d = d { dynObjectSuf_ = f}

setHiSuf :: String -> DynFlags -> DynFlags
setHiSuf f d = d { hiSuf_        = f}

setHieSuf :: String -> DynFlags -> DynFlags
setHieSuf f d = d { hieSuf        = f}

setDynHiSuf :: String -> DynFlags -> DynFlags
setDynHiSuf f d = d { dynHiSuf_     = f}

setOutputFile :: Maybe String -> DynFlags -> DynFlags
setOutputFile f d = d { outputFile_    = f}

setDynOutputFile :: Maybe String -> DynFlags -> DynFlags
setDynOutputFile f d = d { dynOutputFile_ = f}

setOutputHi :: Maybe String -> DynFlags -> DynFlags
setOutputHi f d = d { outputHi       = f}

setDynOutputHi :: Maybe String -> DynFlags -> DynFlags
setDynOutputHi f d = d { dynOutputHi    = f}

parseDynLibLoaderMode :: String -> DynFlags -> DynFlags
parseDynLibLoaderMode f d =
  case splitAt 8 f of
    ("deploy", "") -> d { dynLibLoader = Deployable }
    ("sysdep", "") -> d { dynLibLoader = SystemDependent }
    _ -> throwCsException (CmdLineError ("Unknown dynlib loader: " ++ f))

setDumpPrefixForce :: Maybe String -> DynFlags -> DynFlags
setDumpPrefixForce f d = d { dumpPrefixForce = f }


addOptl :: String -> DynFlags -> DynFlags
addOptl f = alterToolSettings (\s -> s { toolSettings_opt_l   = f : toolSettings_opt_l s})

setDepMakefile :: FilePath -> DynFlags -> DynFlags
setDepMakefile f d = d { depMakefile = f }

setDepIncludePkgDeps :: Bool -> DynFlags -> DynFlags
setDepIncludePkgDeps b d = d { depIncludePkgDeps = b }

addDepExcludeMod :: String -> DynFlags -> DynFlags
addDepExcludeMod m d
    = d { depExcludeMods = mkModuleName m : depExcludeMods d }

addDepSuffix :: FilePath -> DynFlags -> DynFlags
addDepSuffix s d = d { depSuffixes = s : depSuffixes d }

-----------------------------------------------------------------------------
-- Setting the optimisation level

updOptLevelChanged :: Int -> DynFlags -> (DynFlags, Bool)
updOptLevelChanged n dfs
  = (dfs3, changed1 || changed2 || changed3)
  where
   final_n = max 0 (min 2 n)    -- Clamp to 0 <= n <= 2
   (dfs1, changed1) = foldr unset (dfs , False) remove_gopts
   (dfs2, changed2) = foldr set   (dfs1, False) extra_gopts
   (dfs3, changed3) = setLlvmOptLevel dfs2

   extra_gopts  = [ f | (ns,f) <- optLevelFlags, final_n `elem` ns ]
   remove_gopts = [ f | (ns,f) <- optLevelFlags, final_n `notElem` ns ]

   set f (dfs, changed)
     | gopt f dfs = (dfs, changed)
     | otherwise = (gopt_set dfs f, True)

   unset f (dfs, changed)
     | not (gopt f dfs) = (dfs, changed)
     | otherwise = (gopt_unset dfs f, True)

   setLlvmOptLevel dfs
     | llvmOptLevel dfs /= final_n = (dfs{ llvmOptLevel = final_n }, True)
     | otherwise = (dfs, False)

updOptLevel :: Int -> DynFlags -> DynFlags
updOptLevel n = fst . updOptLevelChanged n


{- *********************************************************************
*                                                                      *
                DynFlags parser
*                                                                      *
********************************************************************* -}

parseDynamicFlagsCmdLine
  :: MonadIO m
  => DynFlags
  -> [Located String]
  -> m (DynFlags, [Located String], Messages DriverMessage)
parseDynamicFlagsCmdLine = parseDynamicFlagsFull flagsAll True

newtype CmdLineP s a = CmdLineP (forall m. (Monad m) => StateT s m a)
  deriving (Functor)

instance Applicative (CmdLineP s) where
  pure x = CmdLineP (pure x)
  (<*>) = ap

instance Monad (CmdLineP s) where
  CmdLineP k >>= f = CmdLineP (k >>= \x -> case f x of CmdLineP g -> g)
  return = pure

getCmdLineState :: CmdLineP s s
getCmdLineState = CmdLineP State.get

putCmdLineState :: s -> CmdLineP s ()
putCmdLineState x = CmdLineP (State.put x)

runCmdLineP :: CmdLineP s a -> s -> (a, s)
runCmdLineP (CmdLineP k) s0 = runIdentity $ runStateT k s0

processCmdLineP
  :: forall s m. MonadIO m
  => [Flag (CmdLineP s)]
  -> s
  -> [Located String]
  -> m (([Located String], [Err], [Warn]), s)
processCmdLineP activeFlags s0 args =
  runStateT (processArgs (map (hoistFlag getCmdLineP) activeFlags) args parseResponseFile) s0
  where
    getCmdLineP :: CmdLineP s a -> StateT s m a
    getCmdLineP (CmdLineP k) = k

parseDynamicFlagsFull
  :: MonadIO m
  => [Flag (CmdLineP DynFlags)]
  -> Bool
  -> DynFlags
  -> [Located String]
  -> m (DynFlags, [Located String], Messages DriverMessage)
parseDynamicFlagsFull activeFlags cmdline dflags0 args = do
  ((leftover, errs, cli_warns), dflags1) <- processCmdLineP activeFlags dflags0 args

  let rdr = renderWithContext (initSDocContext dflags0 defaultUserStyle)
  unless (null errs) $ liftIO $ throwCsExceptionIO $ errorsToCsException $
    map ((rdr . ppr . getLoc &&& unLoc) . errMsg) $ errs

  let (dflags2, consistency_warnings) = makeDynFlagsConsistent dflags1

  liftIO $ setUnsafeGlobalDynFlags dflags2

  let diag_opts = initDiagOpts dflags2
      warns = warnsToMessages diag_opts $ mconcat [consistency_warnings, cli_warns]

  return (dflags2, leftover, warns)

{- *********************************************************************
*                                                                      *
                DynFlags specifications
*                                                                      *
********************************************************************* -}

flagsAll :: [Flag (CmdLineP DynFlags)]
flagsAll = map snd flagsAllDeps

flagsAllDeps :: [(Deprecation, Flag (CmdLineP DynFlags))]
flagsAllDeps = package_flags_deps ++ dynamic_flags_deps

----------------Helpers to make flags and keep deprecation information----------

type FlagMaker m = String -> OptKind m -> Flag m

type DynFlagMaker = FlagMaker (CmdLineP DynFlags)

data Deprecation = NotDeprecated | Deprecated
  deriving (Eq, Ord)

make_ord_flag
  :: DynFlagMaker
  -> String
  -> OptKind (CmdLineP DynFlags)
  -> (Deprecation, Flag (CmdLineP DynFlags))
make_ord_flag fm name kind = (NotDeprecated, fm name kind)

----------------------- The main flags themselves ------------------------------

dynamic_flags_deps :: [(Deprecation, Flag (CmdLineP DynFlags))]
dynamic_flags_deps =
  [ make_ord_flag defFlag "v" (OptIntSuffix setVerbosity)
  , make_ord_flag defCsFlag "j" (OptIntSuffix
                               (\n -> case n of
                                   Just n
                                     | n > 0 ->
                                       upd (\d -> d { parMakeCount = Just (ParMakeThisMany n) })
                                     | otherwise -> addErr "Syntax: -j[n] where n > 0"
                                   Nothing ->
                                     upd (\d -> d { parMakeCount = Just ParMakeNumProcessors })))
  , make_ord_flag defCsFlag "jsem" $ hasArg $ \f d ->
                                                d { parMakeCount = Just (ParMakeSemaphore f) }

     -- ways --------------------------------------------------------------------
  , make_ord_flag defCsFlag "prof" (NoArg (addWayDynP WayProf))
  , make_ord_flag defCsFlag "debug" (NoArg (addWayDynP WayDebug))
  , make_ord_flag defCsFlag "threaded" (NoArg (addWayDynP WayThreaded))
  , make_ord_flag defCsFlag "single-threaded" (NoArg (removeWayDynP WayThreaded))

  -- , make_ord_flag defCsFlag "ticky" (NoArg (setGeneralFlag Opt_Ticky >> addWayDynP WayDebug))

    -- Linker -------------------------------------------------------------------
  , make_ord_flag defCsFlag "static" (NoArg (removeWayDynP WayDyn))
  , make_ord_flag defCsFlag "dynamic" (NoArg (addWayDynP WayDyn))
  , make_ord_flag defCsFlag "relative-dynlib-paths"
    (NoArg (setGeneralFlag Opt_RelativeDynlibPaths))
  , make_ord_flag defCsFlag "copy-libs-when-linking"
    (NoArg (setGeneralFlag Opt_SingleLibFolder))
  , make_ord_flag defCsFlag "pie" (NoArg (setGeneralFlag Opt_PICExecutable))
  , make_ord_flag defCsFlag "no-pie" (NoArg (unSetGeneralFlag Opt_PICExecutable))

    -- Specific phases  ---------------------------------------------------------
    -- need to appear before -pgmL to be parsed as LLVM flags.
  , make_ord_flag defFlag "pgmlo"
      $ hasArg $ \f -> alterToolSettings $ \s -> s { toolSettings_pgm_lo  = (f,[]) }
  , make_ord_flag defFlag "pgmlc"
      $ hasArg $ \f -> alterToolSettings $ \s -> s { toolSettings_pgm_lc  = (f,[]) }
  , make_ord_flag defFlag "pgmlas"
      $ hasArg $ \f -> alterToolSettings $ \s -> s { toolSettings_pgm_las  = (f,[]) }
  , make_ord_flag defFlag "pgmlm"
      $ hasArg $ \f -> alterToolSettings $ \s -> s { toolSettings_pgm_lm  =
          if null f then Nothing else Just (f,[]) }
  , make_ord_flag defFlag "pgml"
      $ hasArg $ \f -> alterToolSettings $ \s -> s
         { toolSettings_pgm_l   = (f,[])
         , toolSettings_ccSupportsNoPie = False
         }
  , make_ord_flag defFlag "pgml-supports-no-pie"
      $ noArg $ alterToolSettings $ \s -> s { toolSettings_ccSupportsNoPie = True }
  , make_ord_flag defFlag "pgmwindres"
      $ hasArg $ \f -> alterToolSettings $ \s -> s { toolSettings_pgm_windres = f }
  , make_ord_flag defFlag "pgmar"
      $ hasArg $ \f -> alterToolSettings $ \s -> s { toolSettings_pgm_ar = f }
  , make_ord_flag defFlag "pgmotool"
      $ hasArg $ \f -> alterToolSettings $ \s -> s { toolSettings_pgm_otool = f}
  , make_ord_flag defFlag "pgminstall_name_tool"
      $ hasArg $ \f -> alterToolSettings $ \s -> s { toolSettings_pgm_install_name_tool = f}
  , make_ord_flag defFlag "pgmranlib"
      $ hasArg $ \f -> alterToolSettings $ \s -> s { toolSettings_pgm_ranlib = f }

    -- need to appear before -optl/-opta to be parsed as LLVM flags.
  , make_ord_flag defFlag "optlm"
      $ hasArg $ \f -> alterToolSettings $
                       \s -> s { toolSettings_opt_lm  = f : toolSettings_opt_lm s }
  , make_ord_flag defFlag "optlo"
      $ hasArg $ \f -> alterToolSettings $
                       \s -> s { toolSettings_opt_lo  = f : toolSettings_opt_lo s }
  , make_ord_flag defFlag "optlc"
      $ hasArg $ \f -> alterToolSettings $
                       \s -> s { toolSettings_opt_lc  = f : toolSettings_opt_lc s }
  , make_ord_flag defFlag "optlas"
      $ hasArg $ \f -> alterToolSettings $
                       \s -> s { toolSettings_opt_las  = f : toolSettings_opt_las s }
  , make_ord_flag defFlag "optl"
      (hasArg addOptl)
  , make_ord_flag defFlag "optwindres"
      $ hasArg $ \f -> alterToolSettings $
                       \s -> s { toolSettings_opt_windres = f : toolSettings_opt_windres s }

  , make_ord_flag defCsFlag "split-sections"
    (NoArg $ setGeneralFlag Opt_SplitSections)

    -- csl -M ---------------------------------------------------------------
  , make_ord_flag defCsFlag "dep-suffix" (hasArg addDepSuffix)
  , make_ord_flag defCsFlag "dep-makefile" (hasArg setDepMakefile)
  , make_ord_flag defCsFlag "include-pkg-deps" (noArg (setDepIncludePkgDeps True))
  , make_ord_flag defCsFlag "exclude-module" (hasArg addDepExcludeMod)

    -- Linking --------------------------------------------------------------
  , make_ord_flag defCsFlag "no-link"
        (noArg (\d -> d { csLink=NoLink }))
  , make_ord_flag defCsFlag "shared"
        (noArg (\d -> d { csLink=LinkDynLib }))
  , make_ord_flag defCsFlag "staticlib"
        (noArg (\d -> setGeneralFlag' Opt_LinkRts (d { csLink=LinkStaticLib })))
  , make_ord_flag defCsFlag "-merge-objs"
        (noArg (\d -> d { csLink=LinkMergedObj }))
  , make_ord_flag defCsFlag "dynload" (hasArg parseDynLibLoaderMode)

    -- Libraries ------------------------------------------------------------
  , make_ord_flag defFlag "L"   (Prefix addLibraryPath)
  , make_ord_flag defFlag "l"   (hasArg (addLdInputs . Option . ("-l" ++)))

    -- Output Redirection ---------------------------------------------------
  , make_ord_flag defCsFlag "odir"              (hasArg setObjectDir)
  , make_ord_flag defCsFlag "o"                 (sepArg (setOutputFile . Just))
  , make_ord_flag defCsFlag "dyno"
        (sepArg (setDynOutputFile . Just))
  , make_ord_flag defCsFlag "ohi"
        (hasArg (setOutputHi . Just ))
  , make_ord_flag defCsFlag "dynohi"
        (hasArg (setDynOutputHi . Just ))
  , make_ord_flag defCsFlag "osuf"              (hasArg setObjectSuf)
  , make_ord_flag defCsFlag "dynosuf"           (hasArg setDynObjectSuf)
  , make_ord_flag defCsFlag "hisuf"             (hasArg setHiSuf)
  , make_ord_flag defCsFlag "hiesuf"            (hasArg setHieSuf)
  , make_ord_flag defCsFlag "dynhisuf"          (hasArg setDynHiSuf)
  , make_ord_flag defCsFlag "hidir"             (hasArg setHiDir)
  , make_ord_flag defCsFlag "hiedir"            (hasArg setHieDir)
  , make_ord_flag defCsFlag "tmpdir"            (hasArg setTmpDir)
  , make_ord_flag defCsFlag "stubdir"           (hasArg setStubDir)
  , make_ord_flag defCsFlag "dumpdir"           (hasArg setDumpDir)
  , make_ord_flag defCsFlag "outputdir"         (hasArg setOutputDir)
  , make_ord_flag defCsFlag "ddump-file-prefix"
        (hasArg (setDumpPrefixForce . Just . flip (++) "."))

  , make_ord_flag defCsFlag "dynamic-too"
        (NoArg (setGeneralFlag Opt_BuildDynamicToo))

    -- Keeping temporary files ----------------------------------------------
  , make_ord_flag defCsFlag "keep-llvm-file"
        (NoArg $ setObjBackend llvmBackend >> setGeneralFlag Opt_KeepLlvmFiles)
  , make_ord_flag defCsFlag "keep-llvm-files"
        (NoArg $ setObjBackend llvmBackend >> setGeneralFlag Opt_KeepLlvmFiles)
     -- This only makes sense as plural
  , make_ord_flag defCsFlag "keep-tmp-files"
        (NoArg (setGeneralFlag Opt_KeepTmpFiles))
  , make_ord_flag defCsFlag "keep-hi-file"
        (NoArg (setGeneralFlag Opt_KeepHiFiles))
  , make_ord_flag defCsFlag "no-keep-hi-file"
        (NoArg (unSetGeneralFlag Opt_KeepHiFiles))
  , make_ord_flag defCsFlag "keep-hi-files"
        (NoArg (setGeneralFlag Opt_KeepHiFiles))
  , make_ord_flag defCsFlag "no-keep-hi-files"
        (NoArg (unSetGeneralFlag Opt_KeepHiFiles))
  , make_ord_flag defCsFlag "keep-o-file"
        (NoArg (setGeneralFlag Opt_KeepOFiles))
  , make_ord_flag defCsFlag "no-keep-o-file"
        (NoArg (unSetGeneralFlag Opt_KeepOFiles))
  , make_ord_flag defCsFlag "keep-o-files"
        (NoArg (setGeneralFlag Opt_KeepOFiles))
  , make_ord_flag defCsFlag "no-keep-o-files"
        (NoArg (unSetGeneralFlag Opt_KeepOFiles))

    -- Miscellaneous --------------------------------------------------------
  , make_ord_flag defCsFlag "no-auto-link-packages"
        (NoArg (unSetGeneralFlag Opt_AutoLinkPackages))
  , make_ord_flag defCsFlag "no-csl-main"
        (NoArg (setGeneralFlag Opt_NoCsMain))
  , make_ord_flag defCsFlag "fno-state-hack"
        (NoArg (setGeneralFlag Opt_G_NoStateHack))
  , make_ord_flag defCsFlag "with-rtsopts"
        (HasArg setRtsOpts)
  , make_ord_flag defCsFlag "rtsopts"
        (NoArg (setRtsOptsEnabled RtsOptsAll))
  , make_ord_flag defCsFlag "rtsopts=all"
        (NoArg (setRtsOptsEnabled RtsOptsAll))
  , make_ord_flag defCsFlag "rtsopts=some"
        (NoArg (setRtsOptsEnabled RtsOptsSafeOnly))
  , make_ord_flag defCsFlag "rtsopts=none"
        (NoArg (setRtsOptsEnabled RtsOptsNone))
  , make_ord_flag defCsFlag "rtsopts=ignore"
        (NoArg (setRtsOptsEnabled RtsOptsIgnore))
  , make_ord_flag defCsFlag "rtsopts=ignoreAll"
        (NoArg (setRtsOptsEnabled RtsOptsIgnoreAll))
  , make_ord_flag defCsFlag "no-rtsopts"
        (NoArg (setRtsOptsEnabled RtsOptsNone))
  , make_ord_flag defCsFlag "no-rtsopts-suggestions"
      (noArg (\d -> d {rtsOptsSuggestions = False}))
  , make_ord_flag defCsFlag "dhex-word-literals"
        (NoArg (setGeneralFlag Opt_HexWordLiterals))

  , make_ord_flag defCsFlag "main-is"              (SepArg setMainIs)
  , make_ord_flag defCsFlag "hpcdir"               (SepArg setOptHpcDir)
  -- , make_ord_flag defCsFlag "ticky-allocd"
  --       (NoArg (setGeneralFlag Opt_Ticky_Allocd))
  -- , make_ord_flag defCsFlag "ticky-LNE"
  --       (NoArg (setGeneralFlag Opt_Ticky_LNE))
  -- , make_ord_flag defCsFlag "ticky-ap-thunk"
  --       (NoArg (setGeneralFlag Opt_Ticky_AP))
  -- , make_ord_flag defCsFlag "ticky-dyn-thunk"
  --       (NoArg (setGeneralFlag Opt_Ticky_Dyn_Thunk))
  -- , make_ord_flag defCsFlag "ticky-tag-checks"
  --       (NoArg (setGeneralFlag Opt_Ticky_Tag))

    -- recompilation checker ------------------------------------------------
  , make_ord_flag defFlag "fmax-errors"
      (intSuffix (\n d -> d { maxErrors = Just (max 1 n) }))
  , make_ord_flag defFlag "fno-max-errors"
      (noArg (\d -> d { maxErrors = Nothing }))
  , make_ord_flag defFlag "freverse-errors"
        (noArg (\d -> d {reverseErrors = True} ))
  , make_ord_flag defFlag "fno-reverse-errors"
        (noArg (\d -> d {reverseErrors = False} ))

    -- Include/Import Paths -------------------------------------------------
  , make_ord_flag defFlag "i"              (OptPrefix addImportPath)
   
    -- Output style options -------------------------------------------------
  , make_ord_flag defFlag "dppr-user-length" (intSuffix (\n d ->
                                                       d { pprUserLength = n }))
  , make_ord_flag defFlag "dppr-cols"        (intSuffix (\n d ->
                                                             d { pprCols = n }))
  , make_ord_flag defFlag "fdiagnostics-color=auto"
      (NoArg (upd (\d -> d { useColor = Auto })))
  , make_ord_flag defFlag "fdiagnostics-color=always"
      (NoArg (upd (\d -> d { useColor = Always })))
  , make_ord_flag defFlag "fdiagnostics-color=never"
      (NoArg (upd (\d -> d { useColor = Never })))

  , make_ord_flag defFlag "fprint-error-index-links=auto"
      (NoArg (upd (\d -> d { useErrorLinks = Auto })))
  , make_ord_flag defFlag "fprint-error-index-links=always"
      (NoArg (upd (\d -> d { useErrorLinks = Always })))
  , make_ord_flag defFlag "fprint-error-index-links=never"
      (NoArg (upd (\d -> d { useErrorLinks = Never })))

  , make_ord_flag defCsFlag "dsuppress-all"
      (NoArg $ do setGeneralFlag Opt_SuppressModulePrefixes
                  setGeneralFlag Opt_SuppressIdInfo
                  setGeneralFlag Opt_SuppressTicks
                  setGeneralFlag Opt_SuppressTypeSignatures
                  setGeneralFlag Opt_SuppressCoreSizes
                  setGeneralFlag Opt_SuppressTimestamps)

    -- Debugging ------------------------------------------------------------
  , make_ord_flag defCsFlag "ddump-core-stats"
        (setDumpFlag Opt_D_dump_core_stats)
  , make_ord_flag defCsFlag "ddump-llvm"
        (NoArg $ setDumpFlag' Opt_D_dump_llvm)
  , make_ord_flag defCsFlag "ddump-ds"
        (setDumpFlag Opt_D_dump_ds)
  , make_ord_flag defCsFlag "ddump-ds-preopt"
        (setDumpFlag Opt_D_dump_ds_preopt)
  , make_ord_flag defCsFlag "ddump-inlinings"
        (setDumpFlag Opt_D_dump_inlinings)
  , make_ord_flag defCsFlag "ddump-verbose-inlinings"
        (setDumpFlag Opt_D_dump_verbose_inlinings)
  , make_ord_flag defCsFlag "ddump-simpl-trace"
        (setDumpFlag Opt_D_dump_simpl_trace)
  , make_ord_flag defCsFlag "ddump-occur-anal"
        (setDumpFlag Opt_D_dump_occur_anal)
  , make_ord_flag defCsFlag "ddump-parsed"
        (setDumpFlag Opt_D_dump_parsed)
  , make_ord_flag defCsFlag "ddump-parsed-ast"
        (setDumpFlag Opt_D_dump_parsed_ast)
  , make_ord_flag defCsFlag "dkeep-comments"
        (NoArg (setGeneralFlag Opt_KeepRawTokenStream))
  , make_ord_flag defCsFlag "ddump-rn"
        (setDumpFlag Opt_D_dump_rn)
  , make_ord_flag defCsFlag "ddump-rn-ast"
        (setDumpFlag Opt_D_dump_rn_ast)
  , make_ord_flag defCsFlag "ddump-simpl"
        (setDumpFlag Opt_D_dump_simpl)
  , make_ord_flag defCsFlag "ddump-simpl-iterations"
      (setDumpFlag Opt_D_dump_simpl_iterations)
  , make_ord_flag defCsFlag "ddump-spec"
        (setDumpFlag Opt_D_dump_spec)
  , make_ord_flag defCsFlag "ddump-spec-constr"
        (setDumpFlag Opt_D_dump_spec_constr)
  , make_ord_flag defCsFlag "ddump-prep"
        (setDumpFlag Opt_D_dump_prep)
  , make_ord_flag defCsFlag "ddump-late-cc"
        (setDumpFlag Opt_D_dump_late_cc)
  , make_ord_flag defCsFlag "ddump-call-arity"
        (setDumpFlag Opt_D_dump_call_arity)
  , make_ord_flag defCsFlag "ddump-exitify"
        (setDumpFlag Opt_D_dump_exitify)
  , make_ord_flag defCsFlag "ddump-dmdanal"
        (setDumpFlag Opt_D_dump_dmdanal)
  , make_ord_flag defCsFlag "ddump-dmd-signatures"
        (setDumpFlag Opt_D_dump_dmd_signatures)
  , make_ord_flag defCsFlag "ddump-cpranal"
        (setDumpFlag Opt_D_dump_cpranal)
  , make_ord_flag defCsFlag "ddump-cpr-signatures"
        (setDumpFlag Opt_D_dump_cpr_signatures)
  , make_ord_flag defCsFlag "ddump-tc"
        (setDumpFlag Opt_D_dump_tc)
  , make_ord_flag defCsFlag "ddump-tc-ast"
        (setDumpFlag Opt_D_dump_tc_ast)
  , make_ord_flag defCsFlag "ddump-hie"
        (setDumpFlag Opt_D_dump_hie)
  , make_ord_flag defCsFlag "ddump-types"
        (setDumpFlag Opt_D_dump_types)
  , make_ord_flag defCsFlag "ddump-cse"
        (setDumpFlag Opt_D_dump_cse)
  , make_ord_flag defCsFlag "ddump-float-out"
        (setDumpFlag Opt_D_dump_float_out)
  , make_ord_flag defCsFlag "ddump-float-in"
        (setDumpFlag Opt_D_dump_float_in)
  , make_ord_flag defCsFlag "ddump-liberate-case"
        (setDumpFlag Opt_D_dump_liberate_case)
  , make_ord_flag defCsFlag "ddump-static-argument-transformation"
        (setDumpFlag Opt_D_dump_static_argument_transformation)
  , make_ord_flag defCsFlag "ddump-rn-trace"
        (setDumpFlag Opt_D_dump_rn_trace)
  , make_ord_flag defCsFlag "ddump-if-trace"
        (setDumpFlag Opt_D_dump_if_trace)
  , make_ord_flag defCsFlag "ddump-cs-trace"
        (setDumpFlag Opt_D_dump_cs_trace)
  , make_ord_flag defCsFlag "ddump-tc-trace"
        (NoArg (do setDumpFlag' Opt_D_dump_tc_trace
                   setDumpFlag' Opt_D_dump_cs_trace))
  , make_ord_flag defCsFlag "ddump-ec-trace"
        (setDumpFlag Opt_D_dump_ec_trace)

  , make_ord_flag defCsFlag "ddump-rn-stats"
        (setDumpFlag Opt_D_dump_rn_stats)
  , make_ord_flag defCsFlag "ddump-simpl-stats"
        (setDumpFlag Opt_D_dump_simpl_stats)
  , make_ord_flag defCsFlag "ddump-bcos"
        (setDumpFlag Opt_D_dump_BCOs)
  , make_ord_flag defCsFlag "dsource-stats"
        (setDumpFlag Opt_D_source_stats)
  , make_ord_flag defCsFlag "dverbose-core2core"
        (NoArg $ setVerbosity (Just 2) >> setDumpFlag' Opt_D_verbose_core2core)
  , make_ord_flag defCsFlag "ddump-hi"
        (setDumpFlag Opt_D_dump_hi)
  , make_ord_flag defCsFlag "ddump-minimal-imports"
        (NoArg (setGeneralFlag Opt_D_dump_minimal_imports))
  , make_ord_flag defCsFlag "ddump-hpc"
        (setDumpFlag Opt_D_dump_ticked) -- back compat
  , make_ord_flag defCsFlag "ddump-ticked"
        (setDumpFlag Opt_D_dump_ticked)
  , make_ord_flag defCsFlag "ddump-mod-cycles"
        (setDumpFlag Opt_D_dump_mod_cycles)
  , make_ord_flag defCsFlag "ddump-mod-map"
        (setDumpFlag Opt_D_dump_mod_map)
  , make_ord_flag defCsFlag "ddump-timings"
        (setDumpFlag Opt_D_dump_timings)
  , make_ord_flag defCsFlag "ddump-to-file"
        (NoArg (setGeneralFlag Opt_DumpToFile))
  , make_ord_flag defCsFlag "ddump-hi-diffs"
        (setDumpFlag Opt_D_dump_hi_diffs)
  , make_ord_flag defCsFlag "ddump-rtti"
        (setDumpFlag Opt_D_dump_rtti)
  , make_ord_flag defCsFlag "dlint"
        (NoArg enableDLint)
  , make_ord_flag defCsFlag "dcore-lint"
        (NoArg (setGeneralFlag Opt_DoCoreLinting))
  , make_ord_flag defCsFlag "dshow-passes"
        (NoArg $ forceRecompile >> (setVerbosity $ Just 2))
  , make_ord_flag defCsFlag "dipe-stats"
        (setDumpFlag Opt_D_ipe_stats)
  , make_ord_flag defCsFlag "dfaststring-stats"
        (setDumpFlag Opt_D_faststring_stats)
  , make_ord_flag defCsFlag "ddump-debug"
        (setDumpFlag Opt_D_dump_debug)
  , make_ord_flag defCsFlag "dppr-debug"
        (setDumpFlag Opt_D_ppr_debug)
  , make_ord_flag defCsFlag "ddebug-output"
        (noArg (flip dopt_unset Opt_D_no_debug_output))
  , make_ord_flag defCsFlag "dno-debug-output"
        (setDumpFlag Opt_D_no_debug_output)
  , make_ord_flag defCsFlag "ddump-faststrings"
        (setDumpFlag Opt_D_dump_faststrings)

    -- Optimisation flags ---------------------------------------------------
  , make_ord_flag defCsFlag "O" (optIntSuffixM (\mb_n -> setOptLevel (mb_n `orElse` 1)))
  , make_ord_flag defFlag "fbinary-blob-threshold"
      (intSuffix (\n d -> d { binBlobThreshold = case fromIntegral n of
                                                    0 -> Nothing
                                                    x -> Just x}))
  , make_ord_flag defFlag "fno-max-relevant-binds"
      (noArg (\d -> d { maxRelevantBinds = Nothing }))

  , make_ord_flag defFlag "fmax-uncovered-patterns"
      (intSuffix (\n d -> d { maxUncoveredPatterns = n }))
  , make_ord_flag defFlag "fmax-pmcheck-models"
      (intSuffix (\n d -> d { maxPmCheckModels = n }))
  , make_ord_flag defFlag "fsimplifier-phases"
      (intSuffix (\n d -> d { simplPhases = n }))
  , make_ord_flag defFlag "fmax-simplifier-iterations"
      (intSuffix (\n d -> d { maxSimplIterations = n }))
  , make_ord_flag defFlag "fsimpl-tick-factor"
      (intSuffix (\n d -> d { simplTickFactor = n }))
  , make_ord_flag defFlag "fspec-constr-threshold"
      (intSuffix (\n d -> d { specConstrThreshold = Just n }))
  , make_ord_flag defFlag "fno-spec-constr-threshold"
      (noArg (\d -> d { specConstrThreshold = Nothing }))
  , make_ord_flag defFlag "fspec-constr-count"
      (intSuffix (\n d -> d { specConstrCount = Just n }))
  , make_ord_flag defFlag "fno-spec-constr-count"
      (noArg (\d -> d { specConstrCount = Nothing }))
  , make_ord_flag defFlag "fspec-constr-recursive"
      (intSuffix (\n d -> d { specConstrRecursive = n }))
  , make_ord_flag defFlag "fliberate-case-threshold"
      (intSuffix (\n d -> d { liberateCaseThreshold = Just n }))
  , make_ord_flag defFlag "fno-liberate-case-threshold"
      (noArg (\d -> d { liberateCaseThreshold = Nothing }))
  , make_ord_flag defFlag "dinline-check"
      (sepArg (\s d -> d { unfoldingOpts = updateReportPrefix (Just s) (unfoldingOpts d)}))
  , make_ord_flag defFlag "freduction-depth"
      (intSuffix (\n d -> d { reductionDepth = treatZeroAsInf n }))
  , make_ord_flag defFlag "fconstraint-solver-iterations"
      (intSuffix (\n d -> d { solverIterations = treatZeroAsInf n }))
  , make_ord_flag defFlag "ffloat-lam-args"
      (intSuffix (\n d -> d { floatLamArgs = Just n }))
  , make_ord_flag defFlag "ffloat-all-lams"
      (noArg (\d -> d { floatLamArgs = Nothing }))
  , make_ord_flag defFlag "fhistory-size"
      (intSuffix (\n d -> d { historySize = n }))

  , make_ord_flag defFlag "funfolding-creation-threshold"
      (intSuffix   (\n d -> d { unfoldingOpts = updateCreationThreshold n (unfoldingOpts d)}))
  , make_ord_flag defFlag "funfolding-use-threshold"
      (intSuffix   (\n d -> d { unfoldingOpts = updateUseThreshold n (unfoldingOpts d)}))
  , make_ord_flag defFlag "funfolding-fun-discount"
      (intSuffix   (\n d -> d { unfoldingOpts = updateFunAppDiscount n (unfoldingOpts d)}))
  , make_ord_flag defFlag "funfolding-dict-discount"
      (intSuffix   (\n d -> d { unfoldingOpts = updateDictDiscount n (unfoldingOpts d)}))

  , make_ord_flag defFlag "funfolding-case-threshold"
      (intSuffix   (\n d -> d { unfoldingOpts = updateCaseThreshold n (unfoldingOpts d)}))
  , make_ord_flag defFlag "funfolding-case-scaling"
      (intSuffix   (\n d -> d { unfoldingOpts = updateCaseScaling n (unfoldingOpts d)}))

    , make_ord_flag defFlag "fmax-worker-args"
      (intSuffix (\n d -> d {maxWorkerArgs = n}))
  , make_ord_flag defCsFlag "dinitial-unique"
      (word64Suffix (\n d -> d { initialUnique = n }))
  , make_ord_flag defCsFlag "dunique-increment"
      (intSuffix (\n d -> d { uniqueIncrement = n }))

    -- Profiling ------------------------------------------------------------
  , make_ord_flag defCsFlag "fprof-auto"
      (noArg (\d -> d { profAuto = ProfAutoAll } ))
  , make_ord_flag defCsFlag "fprof-auto-top"
      (noArg (\d -> d { profAuto = ProfAutoTop } ))
  , make_ord_flag defCsFlag "fprof-auto-exported"
      (noArg (\d -> d { profAuto = ProfAutoExports } ))
  , make_ord_flag defCsFlag "fprof-auto-calls"
      (noArg (\d -> d { profAuto = ProfAutoCalls } ))
  , make_ord_flag defCsFlag "fno-prof-auto"
      (noArg (\d -> d { profAuto = NoProfAuto } ))

  , make_ord_flag defCsFlag "fprof-callers"
         (HasArg setCallerCcFilters)

    -- Compiler flags -------------------------------------------------------
  , make_ord_flag defCsFlag "fllvm"            (NoArg (setObjBackend llvmBackend))

  , make_ord_flag defFlag "fno-code"         (NoArg ((upd $ \d ->
                  d { csLink=NoLink }) >> setBackend noBackend))
  , make_ord_flag defFlag "fobject-code"     $ noArgM $ \dflags -> do
      setBackend $ platformDefaultBackend (targetPlatform dflags)
      liftEwM getCmdLineState

    -- position independent flags  ------------------------------------------
  , make_ord_flag defCsFlag "fPIC"          (NoArg (setGeneralFlag Opt_PIC))
  , make_ord_flag defCsFlag "fno-PIC"       (NoArg (unSetGeneralFlag Opt_PIC))
  , make_ord_flag defCsFlag "fPIE"          (NoArg (setGeneralFlag Opt_PIE))
  , make_ord_flag defCsFlag "fno-PIE"       (NoArg (unSetGeneralFlag Opt_PIE))

    -- Debugging flags ------------------------------------------------------
  , make_ord_flag defCsFlag "g"             (OptIntSuffix setDebugLevel)
  ]
  ++ map (mkFlag turnOn  "d"         setGeneralFlag    ) dFlagsDeps
  ++ map (mkFlag turnOff "dno-"      unSetGeneralFlag  ) dFlagsDeps
  ++ map (mkFlag turnOn  "f"         setGeneralFlag    ) fFlagsDeps
  ++ map (mkFlag turnOff "fno-"      unSetGeneralFlag  ) fFlagsDeps
  ++

    -- Warning flags --------------------------------------------------------
  [ make_ord_flag defFlag "W"       (NoArg (setWarningGroup W_extra))
  , make_ord_flag defFlag "Werror"
               (NoArg (do { setGeneralFlag Opt_WarnIsError
                          ; setFatalWarningGroup W_everything }))
  , make_ord_flag defFlag "Wwarn"
               (NoArg (do { unSetGeneralFlag Opt_WarnIsError
                          ; unSetFatalWarningGroup W_everything }))
                          -- Opt_WarnIsError is still needed to pass -Werror
                          -- to CPP; see runCpp in SysTools
  , make_ord_flag defFlag "w"       (NoArg (unSetWarningGroup W_everything))
  ]

  ++ warningControls setWarningGroup unSetWarningGroup setWErrorWarningGroup
       unSetFatalWarningGroup warningGroupsDeps
  ++ warningControls setWarningFlag unSetWarningFlag setWErrorFlag
       unSetFatalWarningFlag wWarningFlagsDeps
  ++ warningControls setCustomWarningFlag unSetCustomWarningFlag setCustomWErrorFlag
       unSetCustomFatalWarningFlag
       [(NotDeprecated, FlagSpec "warnings-deprecations" defaultWarningCategory nop AllModes)]
   
  ++ [ (NotDeprecated, customOrUnrecognizedWarning "Wno-"       unSetCustomWarningFlag)
     , (NotDeprecated, customOrUnrecognizedWarning "Werror="    setCustomWErrorFlag)
     , (NotDeprecated, customOrUnrecognizedWarning "Wwarn="     unSetCustomFatalWarningFlag)
     , (NotDeprecated, customOrUnrecognizedWarning "Wno-error=" unSetCustomFatalWarningFlag)
     , (NotDeprecated, customOrUnrecognizedWarning "W"          setCustomWarningFlag)
     ]

warningControls
  :: (warn_flag -> DynP ())
  -> (warn_flag -> DynP ())
  -> (warn_flag -> DynP ())
  -> (warn_flag -> DynP ())
  -> [(Deprecation, FlagSpec warn_flag)]
  -> [(Deprecation, Flag (CmdLineP DynFlags))]
warningControls set unset set_werror unset_fatal xs
   = map (mkFlag turnOn "W" set) xs
  ++ map (mkFlag turnOff "Wno-" unset) xs
  ++ map (mkFlag turnOn "Werror=" set_werror) xs
  ++ map (mkFlag turnOn "Wwarn=" unset_fatal) xs
  ++ map (mkFlag turnOn "Wno-error" unset_fatal) xs
  ++ map (mkFlag turnOn "fwarn-" set . hideFlag) xs
  ++ map (mkFlag turnOff "fno-warn-" unset . hideFlag) xs

customOrUnrecognizedWarning :: String -> (WarningCategory -> DynP ()) -> Flag (CmdLineP DynFlags)
customOrUnrecognizedWarning prefix custom = defHiddenFlag prefix (Prefix action)
  where
    action :: String -> DynP ()
    action flag
      | validWarningCategory cat = custom cat
      | otherwise = unrecognized flag
      where
        cat = mkWarningCategory (mkFastString flag)

    unrecognized flag = do
      f <- wopt Opt_WarnUnrecognizedWarningFlags <$> liftEwM getCmdLineState
      when f $ addFlagWarn (DriverUnrecognizedFlag (prefix ++ flag))

package_flags_deps :: [(Deprecation, Flag (CmdLineP DynFlags))]
package_flags_deps =
  [ make_ord_flag defFlag "package-db" (HasArg (addPkgDbRef . PkgDbPath))
  , make_ord_flag defFlag "clear-package-db" (NoArg clearPkgDb)
  , make_ord_flag defFlag "no-global-package-db" (NoArg removeGlobalPkgDb)
  , make_ord_flag defFlag "no-user-package-db" (NoArg removeUserPkgDb)
  , make_ord_flag defFlag "global-package-db" (NoArg (addPkgDbRef GlobalPkgDb))
  , make_ord_flag defFlag "user-package-db" (NoArg (addPkgDbRef UserPkgDb))
  , make_ord_flag defCsFlag "package-name" (HasArg $ \name -> upd (setUnitId name))
  , make_ord_flag defCsFlag "this-unit-id" (hasArg setUnitId)

  , make_ord_flag defCsFlag "working-dir" (hasArg setWorkingDirectory)
  , make_ord_flag defCsFlag "this-package-name" (hasArg setPackageName)
  , make_ord_flag defCsFlag "hidden-module" (HasArg addHiddenModule)
  , make_ord_flag defCsFlag "reexported-module" (HasArg addReexportedModule)

  , make_ord_flag defFlag "package" (HasArg exposePackage)
  , make_ord_flag defFlag "package-id" (HasArg exposePackageId)
  , make_ord_flag defFlag "hide-package" (HasArg hidePackage)
  , make_ord_flag defFlag "hide-all-packages" (NoArg (setGeneralFlag Opt_HideAllPackages))
  , make_ord_flag defFlag "package-env" (HasArg setPackageEnv)
  , make_ord_flag defFlag "ignore-package" (HasArg ignorePackage)
  ]
  where
    setPackageEnv env = upd $ \s -> s { packageEnv = Just env }
  

flagsForCompletion :: [String]
flagsForCompletion = [ '-':flagName flag
                     | flag <- flagsAll
                     , modeFilter (flagCsMode flag)
                     ]
  where
    modeFilter AllModes = True
    modeFilter OnlyCs = True
    modeFilter HiddenFlag = False
                     
data FlagSpec flag = FlagSpec
  { flagSpecName :: String
  , flagSpecFlag :: flag
  , flagSpecAction :: (TurnOnFlag -> DynP ())
  , flagSpecCsMode :: CsFlagMode
  }

flagSpec :: String -> flag -> (Deprecation, FlagSpec flag)
flagSpec name flag = flagSpec' name flag nop

flagSpec' :: String -> flag -> (TurnOnFlag -> DynP ()) -> (Deprecation, FlagSpec flag)
flagSpec' name flag act = (NotDeprecated, FlagSpec name flag act AllModes)

warnSpec :: WarningFlag -> [(Deprecation, FlagSpec WarningFlag)]
warnSpec flag = warnSpec' flag nop

warnSpec' :: WarningFlag -> (TurnOnFlag -> DynP ()) -> [(Deprecation, FlagSpec WarningFlag)]
warnSpec' flag act = [ (NotDeprecated, FlagSpec name flag act AllModes)
                     | name <- NE.toList (warnFlagNames flag)
                     ]

flagHiddenSpec :: String -> flag -> (Deprecation, FlagSpec flag)
flagHiddenSpec name flag = flagHiddenSpec' name flag nop

flagHiddenSpec' :: String -> flag -> (TurnOnFlag -> DynP ()) -> (Deprecation, FlagSpec flag)
flagHiddenSpec' name flag act = (NotDeprecated, FlagSpec name flag act HiddenFlag)

hideFlag :: (Deprecation, FlagSpec a) -> (Deprecation, FlagSpec a)
hideFlag (dep, fs) = (dep, fs { flagSpecCsMode = HiddenFlag })

mkFlag
  :: TurnOnFlag
  -> String
  -> (flag -> DynP ())
  -> (Deprecation, FlagSpec flag)
  -> (Deprecation, Flag (CmdLineP DynFlags))
mkFlag turn_on flagPrefix f (dep, (FlagSpec name flag extra_action mode))
  = ( dep
    , Flag (flagPrefix ++ name) (NoArg (f flag >> extra_action turn_on)) mode)

nop :: TurnOnFlag -> DynP ()
nop _ = return ()

wWarningFlagsDeps :: [(Deprecation, FlagSpec WarningFlag)]
wWarningFlagsDeps = [minBound..maxBound] >>= \x -> case x of
  Opt_WarnDeferredTypeErrors -> warnSpec x
  Opt_WarnDeferredOutOfScopeVariables -> warnSpec x
  Opt_WarnDeprecatedFlags -> warnSpec x
  Opt_WarnDodgyForeignImports -> warnSpec x
  Opt_WarnEmptyEnumerations -> warnSpec x
  Opt_WarnRedundantConstraints -> warnSpec x
  Opt_WarnDuplicateExports -> warnSpec x
  Opt_WarnInaccessibleCode -> warnSpec x
  Opt_WarnIncompletePatterns -> warnSpec x
  Opt_WarnIncompleteUniPatterns -> warnSpec x
  Opt_WarnInconsistentFlags -> warnSpec x
  Opt_WarnInlineRuleShadowing -> warnSpec x
  Opt_WarnIdentities -> warnSpec x
  Opt_WarnMissingFields -> warnSpec x
  Opt_WarnMissingImportList -> warnSpec x
  Opt_WarnMissingExportList -> warnSpec x
  Opt_WarnMissingLocalSignatures -> warnSpec x
  Opt_WarnMissingMethods -> warnSpec x
  Opt_WarnMissingSignatures -> warnSpec x
  Opt_WarnMissingKindSignatures -> warnSpec x
  Opt_WarnMissingPolyKindSignatures -> warnSpec x
  Opt_WarnMissingExportedSignatures -> warnSpec x
  Opt_WarnMonomorphism -> warnSpec x
  Opt_WarnNameShadowing -> warnSpec x
  Opt_WarnOrphans -> warnSpec x
  Opt_WarnOverflowedLiterals -> warnSpec x
  Opt_WarnOverlappingPatterns -> warnSpec x
  Opt_WarnTabs -> warnSpec x
  Opt_WarnTypeDefaults -> warnSpec x
  Opt_WarnTypedHoles -> warnSpec x
  Opt_WarnPartialTypeSignatures -> warnSpec x
  Opt_WarnUnsupportedLlvmVersion -> warnSpec x
  Opt_WarnUnusedForalls -> warnSpec x
  Opt_WarnUnusedImports -> warnSpec x
  Opt_WarnUnusedLocalBinds -> warnSpec x
  Opt_WarnUnusedMatches -> warnSpec x
  Opt_WarnUnusedPatternBinds -> warnSpec x
  Opt_WarnUnusedTopBinds -> warnSpec x
  Opt_WarnUnusedTypePatterns -> warnSpec x
  Opt_WarnMissingHomeModules -> warnSpec x
  Opt_WarnUnrecognizedWarningFlags -> warnSpec x
  Opt_WarnPartialFields -> warnSpec x
  Opt_WarnPrepositiveQualifiedModule -> warnSpec x
  Opt_WarnUnusedPackages -> warnSpec x
  Opt_WarnCompatUnqualifiedImports -> warnSpec x
  Opt_WarnOperatorWhitespace -> warnSpec x
  Opt_WarnUnicodeBidirectionalFormatCharacters -> warnSpec x
  Opt_WarnTermVariableCapture -> warnSpec x
  
warningGroupsDeps :: [(Deprecation, FlagSpec WarningGroup)]
warningGroupsDeps = map mk warningGroups
  where
    mk g = (NotDeprecated, FlagSpec (warningGroupName g) g nop AllModes)

dFlagsDeps :: [(Deprecation, FlagSpec GeneralFlag)]
dFlagsDeps =
  [ flagSpec "ppr-case-as-let" Opt_PprCaseAsLet
  , flagSpec "suppress-ticks"             Opt_SuppressTicks
  , flagSpec "suppress-idinfo"            Opt_SuppressIdInfo
  , flagSpec "suppress-unfoldings"        Opt_SuppressUnfoldings
  , flagSpec "suppress-module-prefixes"   Opt_SuppressModulePrefixes
  , flagSpec "suppress-timestamps"        Opt_SuppressTimestamps
  , flagSpec "suppress-type-signatures"   Opt_SuppressTypeSignatures
  , flagSpec "suppress-uniques"           Opt_SuppressUniques
  , flagSpec "suppress-core-sizes"        Opt_SuppressCoreSizes
  ]

fFlagsDeps :: [(Deprecation, FlagSpec GeneralFlag)]
fFlagsDeps =
  [ flagSpec "call-arity"                       Opt_CallArity
  , flagSpec "exitification"                    Opt_Exitification
  , flagSpec "case-merge"                       Opt_CaseMerge
  , flagSpec "case-folding"                     Opt_CaseFolding
  , flagSpec "cse"                              Opt_CSE
  , flagSpec "cpr-anal"                         Opt_CprAnal
  , flagSpec "defer-diagnostics"                Opt_DeferDiagnostics
  , flagSpec "defer-type-errors"                Opt_DeferTypeErrors
  , flagSpec "defer-typed-holes"                Opt_DeferTypedHoles
  , flagSpec "defer-out-of-scope-variables"     Opt_DeferOutOfScopeVariables
  , flagSpec "diagnostics-show-caret"           Opt_DiagnosticsShowCaret
  , flagSpec "diagnostics-as-json"              Opt_DiagnosticsAsJSON
  , flagSpec "dump-with-ways"                   Opt_DumpWithWays
  , flagSpec "dicts-cheap"                      Opt_DictsCheap
  , flagSpec "do-eta-reduction"                 Opt_DoEtaReduction
  , flagSpec "do-lambda-eta-expansion"          Opt_DoLambdaEtaExpansion
  , flagSpec "do-clever-arg-eta-expansion"      Opt_DoCleverArgEtaExpansion
  , flagSpec "eager-blackholing"                Opt_EagerBlackHoling
  , flagSpec "embed-manifest"                   Opt_EmbedManifest
  , flagSpec "error-spans"                      Opt_ErrorSpans
  , flagSpec "excess-precision"                 Opt_ExcessPrecision
  , flagSpec "expose-all-unfoldings"            Opt_ExposeAllUnfoldings
  , flagSpec "expose-internal-symbols"          Opt_ExposeInternalSymbols
  , flagSpec "external-dynamic-refs"            Opt_ExternalDynamicRefs
  , flagSpec "family-application-cache"         Opt_FamAppCache
  , flagSpec "float-in"                         Opt_FloatIn
  , flagSpec "force-recomp"                     Opt_ForceRecomp
  , flagSpec "ignore-optim-changes"             Opt_IgnoreOptimChanges
  , flagSpec "ignore-hpc-changes"               Opt_IgnoreHpcChanges
  , flagSpec "local-float-out"                  Opt_LocalFloatOut
  , flagSpec "local-float-out-top-level"        Opt_LocalFloatOutTopLevel
  , flagSpec "gen-manifest"                     Opt_GenManifest
  , flagSpec "validate-ide-info"                Opt_ValidateHie
  , flagSpec "helpful-errors"                   Opt_HelpfulErrors
  , flagSpec "hpc"                              Opt_Hpc
  , flagSpec "ignore-asserts"                   Opt_IgnoreAsserts
  , flagSpec "ignore-interface-pragmas"         Opt_IgnoreInterfacePragmas
  , flagSpec "irrefutable-tuples"               Opt_IrrefutableTuples
  , flagSpec "keep-going"                       Opt_KeepGoing
  , flagSpec "late-dmd-anal"                    Opt_LateDmdAnal
  , flagSpec "late-specialise"                  Opt_LateSpecialise
  , flagSpec "liberate-case"                    Opt_LiberateCase
  , flagHiddenSpec "llvm-fill-undef-with-garbage" Opt_LlvmFillUndefWithGarbage
  , flagSpec "loopification"                    Opt_Loopification
  , flagSpec "block-layout-cfg"                 Opt_CfgBlocklayout
  , flagSpec "block-layout-weightless"          Opt_WeightlessBlocklayout
  , flagSpec "omit-interface-pragmas"           Opt_OmitInterfacePragmas
  , flagSpec "omit-yields"                      Opt_OmitYields
  , flagSpec "pre-inlining"                     Opt_SimplPreInlining
  , flagSpec "print-unicode-syntax"             Opt_PrintUnicodeSyntax
  , flagSpec "print-expanded-synonyms"          Opt_PrintExpandedSynonyms
  , flagSpec "print-typechecker-elaboration"    Opt_PrintTypecheckerElaboration
  , flagSpec "prof-cafs"                        Opt_AutoSccsOnIndividualCafs
  , flagSpec "prof-count-entries"               Opt_ProfCountEntries
  , flagSpec "prof-late"                        Opt_ProfLateCcs
  , flagSpec "prof-late-overloaded"             Opt_ProfLateOverloadedCcs
  , flagSpec "prof-late-overloaded-calls"       Opt_ProfLateoverloadedCallsCCs
  , flagSpec "prof-manual"                      Opt_ProfManualCcs
  , flagSpec "prof-late-inline"                 Opt_ProfLateInlineCcs
  , flagSpec "shared-implib"                    Opt_SharedImplib
  , flagSpec "spec-constr"                      Opt_SpecConstr
  , flagSpec "spec-constr-keen"                 Opt_SpecConstrKeen
  , flagSpec "specialise"                       Opt_Specialise
  , flagSpec "specialize"                       Opt_Specialise
  , flagSpec "specialise-aggressively"          Opt_SpecialiseAggressively
  , flagSpec "specialize-aggressively"          Opt_SpecialiseAggressively
  , flagSpec "cross-module-specialise"          Opt_CrossModuleSpecialise
  , flagSpec "cross-module-specialize"          Opt_CrossModuleSpecialise
  , flagSpec "polymorphic-specialisation"       Opt_PolymorphicSpecialisation
  , flagSpec "specialise-incoherents"           Opt_SpecialiseIncoherents
  , flagSpec "inline-generics"                  Opt_InlineGenerics
  , flagSpec "inline-generics-aggressively"     Opt_InlineGenericsAggressively
  , flagSpec "static-argument-transformation"   Opt_StaticArgumentTransformation
  , flagSpec "use-rpaths"                       Opt_RPath
  , flagSpec "write-interface"                  Opt_WriteInterface
  , flagSpec "write-if-simplified-core"         Opt_WriteIfSimplifiedCore
  , flagSpec "write-ide-info"                   Opt_WriteHie
  , flagSpec "version-macros"                   Opt_VersionMacros
  , flagSpec "solve-constant-dicts"             Opt_SolveConstantDicts
  , flagSpec "catch-nonexhaustive-cases"        Opt_CatchNonexhaustiveCases
  , flagSpec "alignment-sanitisation"           Opt_AlignmentSanitisation
  , flagSpec "check-prim-bounds"                Opt_DoBoundsChecking
  , flagSpec "num-constant-folding"             Opt_NumConstantFolding
  , flagSpec "core-constant-folding"            Opt_CoreConstantFolding
  , flagSpec "fast-pap-calls"                   Opt_FastPAPCalls
  , flagSpec "show-warning-groups"              Opt_ShowWarnGroups
  , flagSpec "hide-source-paths"                Opt_HideSourcePaths
  , flagSpec "show-loaded-modules"              Opt_ShowLoadedModules
  , flagSpec "whole-archive-hs-libs"            Opt_WholeArchiveCsLibs
  , flagSpec "keep-cafs"                        Opt_KeepCAFs
  , flagSpec "link-rts"                         Opt_LinkRts
  , flagSpec "show-error-context"               Opt_ShowErrorContext
  , flagSpec "split-sections"                   Opt_SplitSections
  , flagSpec "break-points"                     Opt_InsertBreakpoints
  ]

impliedGFlags :: [(GeneralFlag, TurnOnFlag, GeneralFlag)]
impliedGFlags =
  [ (Opt_DeferTypeErrors, turnOn, Opt_DeferTypedHoles)
  , (Opt_DeferTypeErrors, turnOn, Opt_DeferOutOfScopeVariables)
  , (Opt_WriteIfSimplifiedCore, turnOn, Opt_WriteInterface)
  ] 

impliedOffGFlags :: [(GeneralFlag, TurnOnFlag, GeneralFlag)]
impliedOffGFlags = []

enableDLint :: DynP ()
enableDLint = do
  mapM_ setGeneralFlag dLintFlags
  addWayDynP WayDebug
  where
    dLintFlags :: [GeneralFlag]
    dLintFlags =
      [ Opt_DoCoreLinting
      , Opt_CatchNonexhaustiveCases
      , Opt_LlvmFillUndefWithGarbage
      ]

{- *********************************************************************
*                                                                      *
                DynFlags constructors
*                                                                      *
********************************************************************* -}

type DynP = EwM (CmdLineP DynFlags)

upd :: (DynFlags -> DynFlags) -> DynP ()
upd f = liftEwM (do dflags <- getCmdLineState
                    putCmdLineState $! f dflags)

updM :: (DynFlags -> DynP DynFlags) -> DynP ()
updM f = do dflags <- liftEwM getCmdLineState
            dflags' <- f dflags
            liftEwM $ putCmdLineState $! dflags'

--------------- Constructor functions for OptKind -----------------
noArg :: (DynFlags -> DynFlags) -> OptKind (CmdLineP DynFlags)
noArg fn = NoArg (upd fn)

noArgM :: (DynFlags -> DynP DynFlags) -> OptKind (CmdLineP DynFlags)
noArgM fn = NoArg (updM fn)

hasArg :: (String -> DynFlags -> DynFlags) -> OptKind (CmdLineP DynFlags)
hasArg fn = HasArg (upd . fn)

sepArg :: (String -> DynFlags -> DynFlags) -> OptKind (CmdLineP DynFlags)
sepArg fn = SepArg (upd . fn)

intSuffix :: (Int -> DynFlags -> DynFlags) -> OptKind (CmdLineP DynFlags)
intSuffix fn = IntSuffix (\n -> upd (fn n))

intSuffixM :: (Int -> DynFlags -> DynP DynFlags) -> OptKind (CmdLineP DynFlags)
intSuffixM fn = IntSuffix (\n -> updM (fn n))

word64Suffix :: (Word64 -> DynFlags -> DynFlags) -> OptKind (CmdLineP DynFlags)
word64Suffix fn = Word64Suffix (\n -> upd (fn n))

floatSuffix :: (Float -> DynFlags -> DynFlags) -> OptKind (CmdLineP DynFlags)
floatSuffix fn = FloatSuffix (\n -> upd (fn n))

optIntSuffixM :: (Maybe Int -> DynFlags -> DynP DynFlags)
              -> OptKind (CmdLineP DynFlags)
optIntSuffixM fn = OptIntSuffix (\mi -> updM (fn mi))

setDumpFlag :: DumpFlag -> OptKind (CmdLineP DynFlags)
setDumpFlag dump_flag = NoArg (setDumpFlag' dump_flag)

--------------------------
addWayDynP :: Way -> DynP ()
addWayDynP = upd . addWay'

addWay' :: Way -> DynFlags -> DynFlags
addWay' w dflags0 =
   let platform = targetPlatform dflags0
       dflags1 = dflags0 { targetWays_ = addWay w (targetWays_ dflags0) }
       dflags2 = foldr setGeneralFlag' dflags1
                       (wayGeneralFlags platform w)
       dflags3 = foldr unSetGeneralFlag' dflags2
                       (wayUnsetGeneralFlags platform w)
   in dflags3

removeWayDynP :: Way -> DynP ()
removeWayDynP w = upd (\dfs -> dfs { targetWays_ = removeWay w (targetWays_ dfs) })

--------------------------
setGeneralFlag, unSetGeneralFlag :: GeneralFlag -> DynP ()
setGeneralFlag   f = upd (setGeneralFlag' f)
unSetGeneralFlag f = upd (unSetGeneralFlag' f)

setGeneralFlag' :: GeneralFlag -> DynFlags -> DynFlags
setGeneralFlag' f dflags = foldr ($) (gopt_set dflags f) deps
  where
    deps = [ if turn_on then setGeneralFlag'   d
                        else unSetGeneralFlag' d
           | (f', turn_on, d) <- impliedGFlags, f' == f ]

unSetGeneralFlag' :: GeneralFlag -> DynFlags -> DynFlags
unSetGeneralFlag' f dflags = foldr ($) (gopt_unset dflags f) deps
  where
    deps = [ if turn_on then setGeneralFlag' d
                        else unSetGeneralFlag' d
           | (f', turn_on, d) <- impliedOffGFlags, f' == f ]

--------------------------
setWarningGroup :: WarningGroup -> DynP ()
setWarningGroup g = do
    mapM_ setWarningFlag (warningGroupFlags g)
    when (warningGroupIncludesExtendedWarnings g) $ upd wopt_set_all_custom

unSetWarningGroup :: WarningGroup -> DynP ()
unSetWarningGroup g = do
    mapM_ unSetWarningFlag (warningGroupFlags g)
    when (warningGroupIncludesExtendedWarnings g) $ upd wopt_unset_all_custom

setWErrorWarningGroup :: WarningGroup -> DynP ()
setWErrorWarningGroup g =
  do { setWarningGroup g
     ; setFatalWarningGroup g }

setFatalWarningGroup :: WarningGroup -> DynP ()
setFatalWarningGroup g = do
    mapM_ setFatalWarningFlag (warningGroupFlags g)
    when (warningGroupIncludesExtendedWarnings g) $ upd wopt_set_all_fatal_custom

unSetFatalWarningGroup :: WarningGroup -> DynP ()
unSetFatalWarningGroup g = do
    mapM_ unSetFatalWarningFlag (warningGroupFlags g)
    when (warningGroupIncludesExtendedWarnings g) $ upd wopt_unset_all_fatal_custom

setWarningFlag, unSetWarningFlag :: WarningFlag -> DynP ()
setWarningFlag   f = upd (\dfs -> wopt_set dfs f)
unSetWarningFlag f = upd (\dfs -> wopt_unset dfs f)

setFatalWarningFlag, unSetFatalWarningFlag :: WarningFlag -> DynP ()
setFatalWarningFlag   f = upd (\dfs -> wopt_set_fatal dfs f)
unSetFatalWarningFlag f = upd (\dfs -> wopt_unset_fatal dfs f)

setWErrorFlag :: WarningFlag -> DynP ()
setWErrorFlag flag = do
  setWarningFlag flag
  setFatalWarningFlag flag

setCustomWarningFlag, unSetCustomWarningFlag :: WarningCategory -> DynP ()
setCustomWarningFlag   f = upd (\dfs -> wopt_set_custom dfs f)
unSetCustomWarningFlag f = upd (\dfs -> wopt_unset_custom dfs f)

setCustomFatalWarningFlag, unSetCustomFatalWarningFlag :: WarningCategory -> DynP ()
setCustomFatalWarningFlag   f = upd (\dfs -> wopt_set_fatal_custom dfs f)
unSetCustomFatalWarningFlag f = upd (\dfs -> wopt_unset_fatal_custom dfs f)

setCustomWErrorFlag :: WarningCategory -> DynP ()
setCustomWErrorFlag flag = do
  setCustomWarningFlag flag
  setCustomFatalWarningFlag flag

--------------------------

alterToolSettings :: (ToolSettings -> ToolSettings) -> DynFlags -> DynFlags
alterToolSettings f dynFlags = dynFlags { toolSettings = f (toolSettings dynFlags) }

--------------------------
setDumpFlag' :: DumpFlag -> DynP ()
setDumpFlag' dump_flag
  = do upd (\dfs -> dopt_set dfs dump_flag)
       when want_recomp forceRecompile
    where want_recomp = dump_flag `notElem` [Opt_D_dump_if_trace,
                                             Opt_D_dump_hi_diffs,
                                             Opt_D_no_debug_output]

forceRecompile :: DynP ()
forceRecompile = do
  dfs <- liftEwM getCmdLineState
  when (force_recomp dfs) (setGeneralFlag Opt_ForceRecomp)
  where
    force_recomp dfs = isOneShot (csMode dfs)

setVerbosity :: Maybe Int -> DynP ()
setVerbosity mb_n = upd (\dfs -> dfs{ verbosity = mb_n `orElse` 3 })

setDebugLevel :: Maybe Int -> DynP ()
setDebugLevel mb_n =
  upd (\dfs -> exposeSyms $ dfs{ debugLevel = n })
  where
    n = mb_n `orElse` 2
    exposeSyms
      | n > 2     = setGeneralFlag' Opt_ExposeInternalSymbols
      | otherwise = id

addPkgDbRef :: PkgDbRef -> DynP ()
addPkgDbRef p = upd $ \s ->
  s { packageDBFlags = PackageDB p : packageDBFlags s }

removeUserPkgDb :: DynP ()
removeUserPkgDb = upd $ \s ->
  s { packageDBFlags = NoUserPackageDB : packageDBFlags s }

removeGlobalPkgDb :: DynP ()
removeGlobalPkgDb = upd $ \s ->
 s { packageDBFlags = NoGlobalPackageDB : packageDBFlags s }

clearPkgDb :: DynP ()
clearPkgDb = upd $ \s ->
  s { packageDBFlags = ClearPackageDBs : packageDBFlags s }

parsePackageFlag :: String
                 -> ReadP PackageArg
                 -> String          
                 -> PackageFlag
parsePackageFlag flag arg_parse str
 = case filter ((=="").snd) (readP_to_S parse str) of
    [(r, "")] -> r
    _ -> throwCsException $ CmdLineError ("Can't parse package flag: " ++ str)
  where doc = flag ++ " " ++ str
        parse = do
            pkg_arg <- tok arg_parse
            let mk_expose = ExposePackage doc pkg_arg
            ( do _ <- tok $ string "with"
                 fmap (mk_expose . ModRenaming True) parseRns
             <++ fmap (mk_expose . ModRenaming False) parseRns
             <++ return (mk_expose (ModRenaming True [])))
        parseRns = do _ <- tok $ R.char '('
                      rns <- tok $ sepBy parseItem (tok $ R.char ',')
                      _ <- tok $ R.char ')'
                      return rns
        parseItem = do
            orig <- tok $ parseModuleName
            (do _ <- tok $ string "as"
                new <- tok $ parseModuleName
                return (orig, new)
              +++
             return (orig, orig))
        tok m = m >>= \x -> skipSpaces >> return x

exposePackage :: String -> DynP ()
exposePackage p = upd (exposePackage' p)

exposePackageId :: String -> DynP ()
exposePackageId p =
  upd (\s -> s{ packageFlags =
    parsePackageFlag "-package-id" parseUnitArg p : packageFlags s })

hidePackage :: String -> DynP ()
hidePackage p =
  upd (\s -> s{ packageFlags = HidePackage p : packageFlags s })

ignorePackage :: String -> DynP ()
ignorePackage p =
  upd (\s -> s{ ignorePackageFlags = IgnorePackage p : ignorePackageFlags s })

exposePackage' :: String -> DynFlags -> DynFlags
exposePackage' p dflags
    = dflags { packageFlags =
            parsePackageFlag "-package" parsePackageArg p : packageFlags dflags }

parsePackageArg :: ReadP PackageArg
parsePackageArg =
    fmap PackageArg (munch1 (\c -> isAlphaNum c || c `elem` ":-_."))

parseUnitArg :: ReadP PackageArg
parseUnitArg =
    fmap UnitIdArg parseUnit

setUnitId :: String -> DynFlags -> DynFlags
setUnitId p d = d { homeUnitId_ = stringToUnitId p }

setWorkingDirectory :: String -> DynFlags -> DynFlags
setWorkingDirectory p d = d { workingDirectory =  Just p }

augmentByWorkingDirectory :: DynFlags -> FilePath -> FilePath
augmentByWorkingDirectory dflags fp | isRelative fp, Just offset <- workingDirectory dflags
  = offset </> fp
augmentByWorkingDirectory _ fp = fp

setPackageName :: String -> DynFlags -> DynFlags
setPackageName p d = d { thisPackageName =  Just p }

addHiddenModule :: String -> DynP ()
addHiddenModule p =
  upd (\s -> s{ hiddenModules  = Set.insert (mkModuleName p) (hiddenModules s) })

addReexportedModule :: String -> DynP ()
addReexportedModule p =
  upd (\s -> s{ reexportedModules  = Set.insert (mkModuleName p) (reexportedModules s) })

setBackend :: Backend -> DynP ()
setBackend l = upd $ \ dfs ->
  if csLink dfs /= LinkBinary || backendWritesFiles l
  then dfs{ backend = l }
  else dfs

setObjBackend :: Backend -> DynP ()
setObjBackend l = updM set
  where
   set dflags
     | backendWritesFiles (backend dflags)
       = return $ dflags { backend = l }
     | otherwise = return dflags

setOptLevel :: Int -> DynFlags -> DynP DynFlags
setOptLevel n dflags = return (updOptLevel n dflags)

setCallerCcFilters :: String -> DynP ()
setCallerCcFilters arg =
  case parseCallerCcFilter arg of
    Right filt -> upd $ \d -> d { callerCcFilters = filt : callerCcFilters d }
    Left err -> addErr err

setMainIs :: String -> DynP ()
setMainIs arg
  | x:_ <- main_fn, isLower x  -- The arg looked like "Foo.Bar.baz"
  = upd $ \d -> d { mainFunIs = Just main_fn,
                    mainModuleNameIs = mkModuleName main_mod }

  | x:_ <- arg, isUpper x  -- The arg looked like "Foo" or "Foo.Bar"
  = upd $ \d -> d { mainModuleNameIs = mkModuleName arg }

  | otherwise                   -- The arg looked like "baz"
  = upd $ \d -> d { mainFunIs = Just arg }
  where
    (main_mod, main_fn) = splitLongestPrefix arg (== '.')

addLdInputs :: Option -> DynFlags -> DynFlags
addLdInputs p dflags = dflags{ldInputs = ldInputs dflags ++ [p]}

-- -----------------------------------------------------------------------------
-- Load dynflags from environment files.

setFlagsFromEnvFile :: FilePath -> String -> DynP ()
setFlagsFromEnvFile envfile content = do
  setGeneralFlag Opt_HideAllPackages
  parseEnvFile envfile content

parseEnvFile :: FilePath -> String -> DynP ()
parseEnvFile envfile = mapM_ parseEntry . lines
  where
    parseEntry str = case words str of
      ("package-db":_) -> addPkgDbRef (PkgDbPath (envdir </> db))
        where
          envdir = takeDirectory envfile
          db = drop 11 str
      ["clear-package-db"] -> clearPkgDb
      ["hide-package", pkg] -> hidePackage pkg
      ["global-package-db"] -> addPkgDbRef GlobalPkgDb
      ["user-package-db"] -> addPkgDbRef UserPkgDb
      ["pakcage-id", pkgid] -> exposePackageId pkgid
      (('-':'-':_):_) -> return () 
      [] -> return ()
      _ -> throwCsException $ CmdLineError $
           "Can't parse environment file entry: "
           ++ envfile ++ ": " ++ str

-----------------------------------------------------------------------------
-- Paths & Libraries

-- -i on its own deletes the import paths
addImportPath :: FilePath -> DynP ()
addImportPath "" = upd (\s -> s{importPaths = []})
addImportPath p  = upd (\s -> s{importPaths = importPaths s ++ splitPathList p})

addLibraryPath :: FilePath -> DynP ()
addLibraryPath p =
  upd (\s -> s{libraryPaths = libraryPaths s ++ splitPathList p})

split_marker :: Char
split_marker = ':'

splitPathList :: String -> [String]
splitPathList s = filter notNull (splitUp s)
  where
    splitUp xs = split split_marker xs

-- -----------------------------------------------------------------------------
-- tmpDir, where we store temporary files.

setTmpDir :: FilePath -> DynFlags -> DynFlags
setTmpDir dir d = d { tmpDir = TempDir (normalise dir) }

-----------------------------------------------------------------------------
-- RTS opts

setRtsOpts :: String -> DynP ()
setRtsOpts arg  = upd $ \ d -> d {rtsOpts = Just arg}

setRtsOptsEnabled :: RtsOptsEnabled -> DynP ()
setRtsOptsEnabled arg  = upd $ \ d -> d {rtsOptsEnabled = arg}

-----------------------------------------------------------------------------
-- Hpc stuff

setOptHpcDir :: String -> DynP ()
setOptHpcDir arg  = upd $ \ d -> d {hpcDir = arg}

-- -----------------------------------------------------------------------------
-- Compiler Info

compilerInfo :: DynFlags -> [(String, String)]
compilerInfo dflags
  = ("Project name", cProjectName)
  : map (fmap $ expandDirectories (topDir dflags) (toolDir dflags))
        (rawSettings dflags)
  ++ [ ("Project version", projectVersion dflags)
     , ("Project Git commit id", cProjectGitCommitId)
     , ("Project Version Int", cProjectVersionInt)
     , ("Project Unit Id", cProjectUnitId)

     , ("Object splitting supported", showBool False)
     , ("Support dynamic-too", showBool $ not isWindows)
     , ("Support reexported-modules", "YES")
     , ("Support thinning and renaming package flags", "YES")
     , ("Requires unified installed package IDs", "YES")
     , ("Uses unit IDs", "YES")
     , ("Debug on", showBool debugIsOn)
     , ("LibDir", topDir dflags)
     , ("Global Package DB", globalPackageDatabasePath dflags)
     ]
  where
    showBool True = "YES"
    showBool False = "NO"
    platform = targetPlatform dflags
    isWindows = False
    useInplaceMinGW = toolSettings_useInplaceMinGW $ toolSettings dflags
    expandDirectories :: FilePath -> Maybe FilePath -> String -> String
    expandDirectories topd mtoold = expandToolDir useInplaceMinGW mtoold . expandTopDir topd

makeDynFlagsConsistent :: DynFlags -> (DynFlags, [Warn])
makeDynFlagsConsistent dflags
  | ways dflags `hasWay` WayDyn && gopt Opt_BuildDynamicToo dflags
  = let dflags' = gopt_unset dflags Opt_BuildDynamicToo
        warn = "-dynamic-too is ignored when using -dynamic"
    in loop dflags' warn

  | gopt Opt_SplitSections dflags
  , platformHasSubsectionsViaSymbols (targetPlatform dflags)
  = let dflags' = gopt_unset dflags Opt_SplitSections
        warn = "-fsplit-sections is not useful on this platform "
               ++ "since it uses subsections-via-symbols. Ignoring."
    in loop dflags' warn
       
  | backendUnregisterisedAbiOnly (backend dflags)
    && not (platformUnregisterised (targetPlatform dflags))
  = pgmError (backendDescription (backend dflags) ++
              " supports only unregisterised ABI but target platform doesn't use it.")

  | gopt Opt_Hpc dflags && not (backendSupportsHpc (backend dflags))
  = let dflags' = gopt_unset dflags Opt_Hpc
        warn = "Hpc can't be used with " ++ backendDescription (backend dflags) ++
               ". Ignoring -fhpc."
    in loop dflags' warn

  | platformUnregisterised (targetPlatform dflags)
  = pgmError "platformUnregisterised not supported (no ViaC backend)"

  | not (osElfTarget os) && gopt Opt_PIE dflags
  = loop (gopt_unset dflags Opt_PIE)
         "Position-independent only supported on ELF platforms"

  | LinkMergedObj <- csLink dflags
  , Nothing <- outputFile dflags
  = pgmError "--output must be specified when useing --merge-objs"

  | otherwise = (dflags, mempty)
  where
    loc = mkGeneralSrcSpan (fsLit "when making flags consistent")
    loop updated_dflags warning
      = case makeDynFlagsConsistent updated_dflags of
          (dflags', ws) -> (dflags', L loc (DriverInconsistentDynFlags warning) : ws)
    platform = targetPlatform dflags
    arch = platformArch platform
    os = platformOS platform


setUnsafeGlobalDynFlags :: DynFlags -> IO ()
setUnsafeGlobalDynFlags dflags = do
  writeIORef v_unsafeHasPprDebug (hasPprDebug dflags)
  writeIORef v_unsafeHasNoDebugOutput (hasNoDebugOutput dflags)
  writeIORef v_unsafeHasNoStateHack (hasNoStateHack dflags)

outputFile :: DynFlags -> Maybe String
outputFile dflags
  | dynamicNow dflags = dynOutputFile_ dflags
  | otherwise = outputFile_ dflags

updatePlatformConstants :: DynFlags -> Maybe PlatformConstants -> IO DynFlags
updatePlatformConstants dflags mconstants = 
  let platform1 = (targetPlatform dflags) { platform_constants = mconstants }
      dflags1 = dflags { targetPlatform = platform1 }
  in pure dflags1
