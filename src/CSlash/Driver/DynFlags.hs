module CSlash.Driver.DynFlags
  ( DumpFlag(..)
  , GeneralFlag(..)
  , WarningFlag(..), DiagnosticReason(..)
  , FatalMessager, FlushOut(..)
  , ProfAuto(..)
  , hasPprDebug, hasNoDebugOutput, hasNoStateHack
  , dopt, dopt_set, dopt_unset
  , gopt, gopt_set, gopt_unset
  , wopt, wopt_set, wopt_unset
  , wopt_fatal, wopt_set_fatal, wopt_unset_fatal
  , wopt_set_all_custom, wopt_unset_all_custom
  , wopt_set_all_fatal_custom, wopt_unset_all_fatal_custom
  , wopt_set_custom, wopt_unset_custom
  , wopt_set_fatal_custom, wopt_unset_fatal_custom
  , DynFlags(..)
  , ParMakeCount(..)
  , ways
  , HasDynFlags(..), ContainsDynFlags(..)
  , RtsOptsEnabled(..)
  , CsMode(..), isOneShot
  , CsLink(..)
  , PackageFlag(..), PackageArg(..), ModRenaming(..)
  , IgnorePackageFlag(..)
  , PackageDBFlag(..), PkgDbRef(..)
  , Option(..), showOpt
  , DynLibLoader(..)

  , defaultDynFlags
  , initDynFlags
  , defaultFatalMessager
  , defaultFlushOut
  , optLevelFlags

  , TurnOnFlag
  , turnOn
  , turnOff

  , projectVersion
  , topDir, toolDir
  , globalPackageDatabasePath

  , IncludeSpecs(..), addGlobalInclude

  , initSDocContext
  ) where

import CSlash.Platform
import CSlash.Platform.Ways
-- import GHC.Platform.Profile

-- import GHC.CmmToAsm.CFG.Weight
import CSlash.Core.Unfold
import CSlash.Data.Bool
import CSlash.Data.EnumSet (EnumSet)
import CSlash.Data.Maybe
import CSlash.Builtin.Names ( mAIN_NAME )
import CSlash.Driver.Backend
import CSlash.Driver.Flags
import CSlash.Driver.Phases ( Phase(..), phaseInputExt )
-- import GHC.Driver.Plugins.External
import CSlash.Settings
import CSlash.Settings.Constants
import CSlash.Types.Basic ( IntWithInf, treatZeroAsInf )
import CSlash.Types.Error (DiagnosticReason(..))
import CSlash.Types.ProfAuto
-- import GHC.Types.SafeHaskell
import CSlash.Types.SrcLoc
import CSlash.Unit.Module
import CSlash.Unit.Module.Warnings
import CSlash.Utils.CliOption
import CSlash.SysTools.Terminal ( stderrSupportsAnsiColors )
-- import GHC.UniqueSubdir (uniqueSubdir)
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.TmpFs

-- import qualified GHC.Types.FieldLabel as FieldLabel
import qualified CSlash.Utils.Ppr.Color as Col
import qualified CSlash.Data.EnumSet as EnumSet

import CSlash.Core.Opt.CallerCC.Types

import Control.Monad (msum, (<=<))
-- import Control.Monad.Trans.Class (lift)
-- import Control.Monad.Trans.Except (ExceptT)
-- import Control.Monad.Trans.Reader (ReaderT)
-- import Control.Monad.Trans.Writer (WriterT)
import Data.Word
import System.IO
import System.IO.Error (catchIOError)
import System.Environment (lookupEnv)
import System.FilePath (normalise, (</>))
import System.Directory
import GHC.Foreign (withCString, peekCString)

import qualified Data.Set as Set

-- import qualified GHC.LanguageExtensions as LangExt

-- -----------------------------------------------------------------------------
-- DynFlags

data DynFlags = DynFlags
  { csMode :: CsMode
  , csLink :: CsLink
  , backend :: !Backend

  , csNameVersion :: {-# UNPACK #-} !CsNameVersion
  , fileSettings :: {-# UNPACK #-} !FileSettings
  , targetPlatform :: Platform
  , toolSettings :: {-# UNPACK #-} !ToolSettings
  , platformMisc :: {-# UNPACK #-} !PlatformMisc
  , rawSettings :: [(String, String)]
  , tmpDir :: TempDir

  , llvmOptLevel :: Int
  , verbosity :: Int
  , debugLevel :: Int
  , simplPhases :: Int
  , maxSimplIterations :: Int
  , ruleCheck :: Maybe String

  , parMakeCount :: Maybe ParMakeCount

  , enableTimeStats :: Bool

  , maxRelevantBinds :: Maybe Int
  -- , maxValidHoleFits :: Maybe Int
  -- , maxRefHoleFits :: Maybe Int
  -- , refLevelHoleFits :: Maybe Int
  , maxUncoveredPatterns :: Int
  , maxPmCheckModels :: Int
  , simplTickFactor :: Int
  , specConstrThreshold :: Maybe Int
  , specConstrCount :: Maybe Int
  , specConstrRecursive :: Int
  , binBlobThreshold :: Maybe Word
  , liberateCaseThreshold :: Maybe Int
  , floatLamArgs :: Maybe Int

  , liftLamsRecArgs :: Maybe Int
  , liftLamsNonRecArgs :: Maybe Int
  , liftLamsKnown :: Bool

  , historySize :: Int

  , importPaths :: [FilePath]
  , mainModuleNameIs :: ModuleName
  , mainFunIs :: Maybe String
  , reductionDepth :: IntWithInf
  , solverIterations :: IntWithInf
  -- , givensFuel :: Int
  -- , wantedsFuel :: Int
  -- , qcsFuel :: Int
  , homeUnitId_ :: UnitId
  , homeUnitInstanceOf_ :: Maybe UnitId
  , homeUnitInstantiations_ :: [(ModuleName, Module)]

  , workingDirectory :: Maybe FilePath
  , thisPackageName :: Maybe String
  , hiddenModules :: Set.Set ModuleName
  , reexportedModules :: Set.Set ModuleName

  , targetWays_ :: Ways

  , splitInfo :: Maybe (String, Int)

  , objectDir :: Maybe String
  , dylibInstallName :: Maybe String
  , hiDir :: Maybe String
  , hieDir :: Maybe String
  , stubDir :: Maybe String
  , dumpDir :: Maybe String

  , objectSuf_ :: String
  , hiSuf_ :: String
  , hieSuf :: String

  , dynObjectSuf_ :: String
  , dynHiSuf_ :: String

  , outputFile_ :: Maybe String
  , dynOutputFile_ :: Maybe String
  , outputHi :: Maybe String
  , dynOutputHi :: Maybe String
  , dynLibLoader :: DynLibLoader

  , dynamicNow :: !Bool

  , dumpPrefix :: FilePath

  , dumpPrefixForce :: Maybe FilePath

  , ldInputs :: [Option]

  , includePaths :: IncludeSpecs
  , libraryPaths :: [String]

  , rtsOpts :: Maybe String
  , rtsOptsEnabled :: RtsOptsEnabled
  , rtsOptsSuggestions :: Bool

  , hpcDir :: String

  , depMakefile :: FilePath
  , depIncludePkgDeps :: Bool
  , depExcludeMods :: [ModuleName]
  , depSuffixes :: [String]

  ,  packageDBFlags :: [PackageDBFlag]

  , ignorePackageFlags :: [IgnorePackageFlag]
  , packageFlags :: [PackageFlag]
  , packageEnv :: Maybe FilePath

  , dumpFlags :: EnumSet DumpFlag
  , generalFlags :: EnumSet GeneralFlag
  , warningFlags :: EnumSet WarningFlag
  , fatalWarningFlags :: EnumSet WarningFlag
  , customWarningCategories :: WarningCategorySet
  , fatalCustomWarningCategories :: WarningCategorySet

  , unfoldingOpts :: !UnfoldingOpts

  , maxWorkerArgs :: Int

  , flushOut :: FlushOut

  , csVersionFile :: Maybe FilePath

  , pprUserLength :: Int
  , pprCols :: Int

  , useUnicode :: Bool
  , useColor :: OverridingBool
  , canUseColor :: Bool
  , useErrorLinks :: OverridingBool
  , canUseErrorLinks :: Bool
  , colScheme :: Col.Scheme

  , profAuto :: ProfAuto
  , callerCcFilters :: [CallerCcFilter]

  , interactivePrint :: Maybe String

  , reverseErrors :: Bool

  , maxErrors :: Maybe Int

  , initialUnique :: Word64
  , uniqueIncrement :: Int
  }

class HasDynFlags m where
  getDynFlags :: m DynFlags

class ContainsDynFlags t where
  extractDynFlags :: t -> DynFlags

-----------------------------------------------------------------------------

initDynFlags :: DynFlags -> IO DynFlags
initDynFlags dflags = do
  canUseUnicode <- do let enc = localeEncoding
                          str = "‘’"
                      (withCString enc str $ \cstr ->
                          do str' <- peekCString enc cstr
                             return (str == str'))
                        `catchIOError` \_ -> return False
  csNoUnicodeEnv <- lookupEnv "CS_NO_UNICODE"
  let useUnicode' = isNothing csNoUnicodeEnv && canUseUnicode
  maybeCsColorsEnv <- lookupEnv "Cs_COLORS"
  let adjustCols (Just env) = Col.parseScheme env
      adjustCols Nothing = id
  let (useColor', colScheme') = adjustCols maybeCsColorsEnv (useColor dflags, colScheme dflags)
  tmp_dir <- normalise <$> getTemporaryDirectory
  return dflags { useUnicode = useUnicode'
                , useColor = useColor'
                , canUseColor = stderrSupportsAnsiColors
                , canUseErrorLinks = stderrSupportsAnsiColors
                , colScheme = colScheme'
                , tmpDir = TempDir tmp_dir
                }

defaultDynFlags :: Settings -> DynFlags
defaultDynFlags mySettings = DynFlags
  { csMode = CompManager
  , csLink = LinkBinary
  , backend = platformDefaultBackend (sTargetPlatform mySettings)

  , csNameVersion = sCsNameVersion mySettings
  , fileSettings = sFileSettings mySettings
  , targetPlatform = sTargetPlatform mySettings
  , toolSettings = sToolSettings mySettings
  , platformMisc = sPlatformMisc mySettings
  , rawSettings = sRawSettings mySettings
  , tmpDir = panic "defaultDynFlags: uninitialized tmpDir"

  , llvmOptLevel = 0
  , verbosity = 0
  , debugLevel = 0
  , simplPhases = 2
  , maxSimplIterations = 4
  , ruleCheck = Nothing

  , parMakeCount = Nothing

  , enableTimeStats = False

  , maxRelevantBinds = Just 6
  -- , maxValidHoleFits = Just 6
  -- , maxRefHoleFits = Just 6
  -- , refLevelHoleFits = Nothing
  , maxUncoveredPatterns = 4
  , maxPmCheckModels = 30
  , simplTickFactor = 100
  , specConstrThreshold = Just 2000
  , specConstrCount = Just 3
  , specConstrRecursive = 3
  , binBlobThreshold = Just 500000
  , liberateCaseThreshold = Just 2000
  , floatLamArgs = Just 0

  , liftLamsRecArgs = Just 5
  , liftLamsNonRecArgs = Just 5
  , liftLamsKnown = False

  , historySize = 20

  , importPaths = ["."]
  , mainModuleNameIs = mAIN_NAME
  , mainFunIs = Nothing
  , reductionDepth = treatZeroAsInf mAX_REDUCTION_DEPTH
  , solverIterations = treatZeroAsInf mAX_SOLVER_ITERATIONS
  -- , givensFuel = 
  -- , wantedsFuel =
  -- , qcsFuel =
  , homeUnitId_ = mainUnitId
  , homeUnitInstanceOf_ = Nothing
  , homeUnitInstantiations_ = []

  , workingDirectory = Nothing
  , thisPackageName = Nothing
  , hiddenModules = Set.empty
  , reexportedModules = Set.empty

  , targetWays_ = Set.empty

  , splitInfo = Nothing

  , objectDir = Nothing
  , dylibInstallName = Nothing
  , hiDir = Nothing
  , hieDir = Nothing
  , stubDir = Nothing
  , dumpDir = Nothing

  , objectSuf_ = phaseInputExt StopLn
  , hiSuf_ = "hi"
  , hieSuf = "hie"

  , dynObjectSuf_ = "dyn_" ++ phaseInputExt StopLn
  , dynHiSuf_ = "dyn_hi"

  , outputFile_ = Nothing
  , dynOutputFile_ = Nothing
  , outputHi = Nothing
  , dynOutputHi = Nothing
  , dynLibLoader = SystemDependent

  , dynamicNow = False

  , dumpPrefix = "non-module."

  , dumpPrefixForce = Nothing

  , ldInputs = []

  , includePaths = IncludeSpecs [] [] []
  , libraryPaths = []

  , rtsOpts = Nothing
  , rtsOptsEnabled = RtsOptsSafeOnly
  , rtsOptsSuggestions = True

  , hpcDir = ".hpc"

  , depMakefile = "Makefile"
  , depIncludePkgDeps = False
  , depExcludeMods = []
  , depSuffixes = []

  ,  packageDBFlags = []

  , ignorePackageFlags = []
  , packageFlags = []
  , packageEnv = Nothing

  , dumpFlags = EnumSet.empty
  , generalFlags = EnumSet.fromList (defaultFlags mySettings)
  , warningFlags = EnumSet.fromList standardWarnings
  , fatalWarningFlags = EnumSet.empty
  , customWarningCategories = completeWarningCategorySet
  , fatalCustomWarningCategories = emptyWarningCategorySet

  , unfoldingOpts = defaultUnfoldingOpts

  , maxWorkerArgs = 10

  , flushOut = defaultFlushOut

  , csVersionFile = Nothing

  , pprUserLength = 5
  , pprCols = 100

  , useUnicode = False
  , useColor = Auto
  , canUseColor = False
  , useErrorLinks = Auto
  , canUseErrorLinks = False
  , colScheme = Col.defaultScheme

  , profAuto = NoProfAuto
  , callerCcFilters = []

  , interactivePrint = Nothing

  , reverseErrors = False

  , maxErrors = Nothing

  , initialUnique = 0
  , uniqueIncrement = 1
  }

type FatalMessager = String -> IO ()

defaultFatalMessager :: FatalMessager
defaultFatalMessager = hPutStrLn stderr

newtype FlushOut = FlushOut (IO ())

defaultFlushOut :: FlushOut
defaultFlushOut = FlushOut $ hFlush stdout

data ParMakeCount
  = ParMakeThisMany Int
  | ParMakeNumProcessors
  | ParMakeSemaphore FilePath

data CsMode
  = CompManager
  | OneShot
  | MkDepend
  deriving Eq

instance Outputable CsMode where
  ppr CompManager = text "CompManager"
  ppr OneShot = text "OneShot"
  ppr MkDepend = text "MkDepend"

isOneShot :: CsMode -> Bool
isOneShot OneShot = True
isOneShot _ = False

data CsLink
  = NoLink
  | LinkBinary
  | LinkInMemory
  | LinkDynLib
  | LinkStaticLib
  | LinkMergedObj
  deriving (Eq, Show)

data PackageArg
  = PackageArg String
  | UnitIdArg Unit
  deriving (Eq, Show)

instance Outputable PackageArg where
  ppr (PackageArg pn) = text "package" <+> text pn
  ppr (UnitIdArg uid) = text "unit" <+> ppr uid

data ModRenaming = ModRenaming
  { modRenamingWithImplicit :: Bool
  , modRenamings :: [(ModuleName, ModuleName)]
  }
  deriving (Eq)

instance Outputable ModRenaming where
  ppr (ModRenaming b rns) = ppr b <+> parens (ppr rns)

newtype IgnorePackageFlag = IgnorePackage String
  deriving (Eq)

data PackageFlag
  = ExposePackage String PackageArg ModRenaming
  | HidePackage String
  deriving (Eq)

data PackageDBFlag
  = PackageDB PkgDbRef
  | NoUserPackageDB
  | NoGlobalPackageDB
  | ClearPackageDBs
  deriving (Eq)

data DynLibLoader
  = Deployable
  | SystemDependent
  deriving Eq

data RtsOptsEnabled
  = RtsOptsNone
  | RtsOptsIgnore
  | RtsOptsIgnoreAll
  | RtsOptsSafeOnly
  | RtsOptsAll
  deriving (Show)

data PkgDbRef
  = GlobalPkgDb
  | UserPkgDb
  | PkgDbPath FilePath
  deriving Eq

data IncludeSpecs = IncludeSpecs
  { includePathsQuote :: [String]
  , includePathsGlobal :: [String]
  , includePathsQuoteImplicit :: [String]
  }
  deriving Show

addGlobalInclude :: IncludeSpecs -> [String] -> IncludeSpecs
addGlobalInclude spec paths = let f = includePathsGlobal spec
                              in spec { includePathsGlobal = f ++ paths }

hasPprDebug :: DynFlags -> Bool
hasPprDebug = dopt Opt_D_ppr_debug

hasNoDebugOutput :: DynFlags -> Bool
hasNoDebugOutput = dopt Opt_D_no_debug_output

hasNoStateHack :: DynFlags -> Bool
hasNoStateHack = gopt Opt_G_NoStateHack

dopt :: DumpFlag -> DynFlags -> Bool
dopt = getDumpFlagFrom verbosity dumpFlags

dopt_set :: DynFlags -> DumpFlag -> DynFlags
dopt_set dflags f = dflags{ dumpFlags = EnumSet.insert f (dumpFlags dflags) }

dopt_unset :: DynFlags -> DumpFlag -> DynFlags
dopt_unset dfs f = dfs{ dumpFlags = EnumSet.delete f (dumpFlags dfs) }

gopt :: GeneralFlag -> DynFlags -> Bool
gopt Opt_PIC dflags
  | dynamicNow dflags = True
gopt Opt_ExternalDynamicRefs dflags
  | dynamicNow dflags = True
gopt Opt_SplitSections dflags
  | dynamicNow dflags = False
gopt f dflags = f `EnumSet.member` generalFlags dflags

gopt_set :: DynFlags -> GeneralFlag -> DynFlags
gopt_set dfs f = dfs{ generalFlags = EnumSet.insert f (generalFlags dfs) }

gopt_unset :: DynFlags -> GeneralFlag -> DynFlags
gopt_unset dfs f = dfs{ generalFlags = EnumSet.delete f (generalFlags dfs) }

wopt :: WarningFlag -> DynFlags -> Bool
wopt f dflags = f `EnumSet.member` warningFlags dflags

wopt_set :: DynFlags -> WarningFlag -> DynFlags
wopt_set dfs f = dfs{ warningFlags = EnumSet.insert f (warningFlags dfs) }

wopt_unset :: DynFlags -> WarningFlag -> DynFlags
wopt_unset dfs f = dfs{ warningFlags = EnumSet.delete f (warningFlags dfs) }

wopt_fatal :: WarningFlag -> DynFlags -> Bool
wopt_fatal f dflags = f `EnumSet.member` fatalWarningFlags dflags

wopt_set_fatal :: DynFlags -> WarningFlag -> DynFlags
wopt_set_fatal dfs f
    = dfs { fatalWarningFlags = EnumSet.insert f (fatalWarningFlags dfs) }

wopt_unset_fatal :: DynFlags -> WarningFlag -> DynFlags
wopt_unset_fatal dfs f
    = dfs { fatalWarningFlags = EnumSet.delete f (fatalWarningFlags dfs) }

wopt_set_all_custom :: DynFlags -> DynFlags
wopt_set_all_custom dfs
    = dfs{ customWarningCategories = completeWarningCategorySet }

wopt_unset_all_custom :: DynFlags -> DynFlags
wopt_unset_all_custom dfs
    = dfs{ customWarningCategories = emptyWarningCategorySet }

wopt_set_all_fatal_custom :: DynFlags -> DynFlags
wopt_set_all_fatal_custom dfs
    = dfs { fatalCustomWarningCategories = completeWarningCategorySet }

wopt_unset_all_fatal_custom :: DynFlags -> DynFlags
wopt_unset_all_fatal_custom dfs
    = dfs { fatalCustomWarningCategories = emptyWarningCategorySet }

wopt_set_custom :: DynFlags -> WarningCategory -> DynFlags
wopt_set_custom dfs f = dfs{ customWarningCategories = insertWarningCategorySet f (customWarningCategories dfs) }

wopt_unset_custom :: DynFlags -> WarningCategory -> DynFlags
wopt_unset_custom dfs f = dfs{ customWarningCategories = deleteWarningCategorySet f (customWarningCategories dfs) }

wopt_set_fatal_custom :: DynFlags -> WarningCategory -> DynFlags
wopt_set_fatal_custom dfs f
  = dfs{ fatalCustomWarningCategories =
           insertWarningCategorySet f (fatalCustomWarningCategories dfs) }

wopt_unset_fatal_custom :: DynFlags -> WarningCategory -> DynFlags
wopt_unset_fatal_custom dfs f
  = dfs{ fatalCustomWarningCategories =
           deleteWarningCategorySet f (fatalCustomWarningCategories dfs) }

defaultFlags :: Settings -> [GeneralFlag]
defaultFlags settings
  = [ Opt_AutoLinkPackages
    , Opt_DiagnosticsShowCaret
    , Opt_EmbedManifest
    , Opt_FamAppCache
    , Opt_GenManifest
    , Opt_HelpfulErrors
    , Opt_KeepHiFiles
    , Opt_KeepOFiles
    , Opt_OmitYields
    , Opt_PrintBindContents
    , Opt_ProfCountEntries
    , Opt_SharedImplib
    , Opt_SimplPreInlining
    , Opt_VersionMacros
    , Opt_RPath
    , Opt_DumpWithWays
    , Opt_ShowErrorContext
    , Opt_SpecialiseIncoherents
    ]
    ++ [f | (ns, f) <- optLevelFlags, 0 `elem` ns]
    ++ [Opt_LocalFloatOut, Opt_LocalFloatOutTopLevel]
    ++ default_PIC platform
    where platform = sTargetPlatform settings

optLevelFlags :: [([Int], GeneralFlag)]
optLevelFlags
  = [ ([0,1,2], Opt_DoLambdaEtaExpansion)
    , ([1,2], Opt_DoCleverArgEtaExpansion)
    , ([0,1,2], Opt_DoEtaReduction)
    , ([0,1,2], Opt_ProfManualCcs)

    , ([0], Opt_IgnoreInterfacePragmas)
    , ([0], Opt_OmitInterfacePragmas)

    , ([1,2], Opt_CoreConstantFolding)

    , ([1,2], Opt_CallArity)
    , ([1,2], Opt_Exitification)
    , ([1,2], Opt_CaseMerge)
    , ([1,2], Opt_CaseFolding)

    , ([1,2], Opt_FloatIn)
    , ([1,2], Opt_IgnoreAsserts)
    , ([1,2], Opt_Loopification)
    , ([1,2], Opt_CfgBlocklayout)

    , ([1,2], Opt_Specialise)
    , ([1,2], Opt_CrossModuleSpecialise)
    , ([1,2], Opt_InlineGenerics)
    , ([1,2], Opt_CprAnal)
    , ([1,2], Opt_SolveConstantDicts)
    , ([1,2], Opt_NumConstantFolding)

    , ([2], Opt_LiberateCase)
    , ([2], Opt_SpecConstr)
    , ([2], Opt_FastPAPCalls)
    ]

type TurnOnFlag = Bool

turnOn :: TurnOnFlag
turnOn = True

turnOff :: TurnOnFlag
turnOff = False

default_PIC :: Platform -> [GeneralFlag]
default_PIC platform =
  case (platformOS platform, platformArch platform) of
    (OSLinux, ArchX86_64) -> [Opt_PIC]
    _ -> []

ways :: DynFlags -> Ways
ways dflags
  | dynamicNow dflags = addWay WayDyn (targetWays_ dflags)
  | otherwise = targetWays_ dflags

topDir :: DynFlags -> FilePath
topDir dflags = fileSettings_topDir $ fileSettings dflags

projectVersion :: DynFlags -> String
projectVersion dflags = csNameVersion_projectVersion (csNameVersion dflags)

toolDir :: DynFlags -> Maybe FilePath
toolDir dflags = fileSettings_toolDir $ fileSettings dflags

globalPackageDatabasePath :: DynFlags -> FilePath
globalPackageDatabasePath dflags = fileSettings_globalPackageDatabase $ fileSettings dflags

initSDocContext :: DynFlags -> PprStyle -> SDocContext
initSDocContext dflags style = SDC
  { sdocStyle                       = style
  , sdocColScheme                   = colScheme dflags
  , sdocLastColour                  = Col.colReset
  , sdocShouldUseColor              = overrideWith (canUseColor dflags) (useColor dflags)
  , sdocDefaultDepth                = pprUserLength dflags
  , sdocLineLength                  = pprCols dflags
  , sdocCanUseUnicode               = useUnicode dflags
  , sdocPrintErrIndexLinks          = overrideWith (canUseErrorLinks dflags) (useErrorLinks dflags)
  , sdocHexWordLiterals             = gopt Opt_HexWordLiterals dflags
  , sdocPprDebug                    = dopt Opt_D_ppr_debug dflags
  , sdocPrintUnicodeSyntax          = gopt Opt_PrintUnicodeSyntax dflags
  , sdocPrintCaseAsLet              = gopt Opt_PprCaseAsLet dflags
  , sdocPrintTypecheckerElaboration = gopt Opt_PrintTypecheckerElaboration dflags
  , sdocSuppressTicks               = gopt Opt_SuppressTicks dflags
  , sdocSuppressTypeSignatures      = gopt Opt_SuppressTypeSignatures dflags
  , sdocSuppressIdInfo              = gopt Opt_SuppressIdInfo dflags
  , sdocSuppressUnfoldings          = gopt Opt_SuppressUnfoldings dflags
  , sdocSuppressUniques             = gopt Opt_SuppressUniques dflags
  , sdocSuppressModulePrefixes      = gopt Opt_SuppressModulePrefixes dflags
  , sdocErrorSpans                  = gopt Opt_ErrorSpans dflags
  , sdocPrintTypeAbbreviations      = True
  , sdocUnitIdForUser               = ftext
  }
