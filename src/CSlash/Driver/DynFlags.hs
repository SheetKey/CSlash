module CSlash.Driver.DynFlags
  ( module CSlash.Driver.DynFlags
  , module CSlash.Utils.CliOption
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
-- import GHC.Driver.Phases ( Phase(..), phaseInputExt )
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
-- import GHC.SysTools.Terminal ( stderrSupportsAnsiColors )
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
  { cslMode :: CsMode
  , cslLink :: CsLink
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
  , maxValidHoleFits :: Maybe Int
  , maxRefHoleFits :: Maybe Int
  , refLevelHoleFits :: Maybe Int
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
  , givensFuel :: Int
  , wantedsFuel :: Int
  , qcsFuel :: Int
  , homeUnitId_ :: UnitId
  , homeUnitInstanceOf_ :: Maybe UnitId
  , homeUnitInstantiations_ :: [(ModuleName, Module)]

  , workingDirectory :: Maybe FilePath
  , thisPackageName :: Maybe String
  , hiddenModule :: Set.Set ModuleName
  , reexportedModules :: Set.Set ModuleName

  , tagetWays_ :: Ways

  , splitInfo :: Maybe (String, Int)

  , objectDir :: Maybe String
  , dylibInstallName :: Maybe String
  , hiDire :: Maybe String
  , hieDir :: Maybe String
  , stubDir :: Maybe String
  , dumpDir :: Maybe String

  , objectSuf_ :: String
  , hcSuf :: String
  , hiSuf_ :: String
  , hieSuf :: String

  , dynObjectSuf_ :: String
  , dynHiSuf_ :: String

  , outputFile :: Maybe String
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

  , unfoldinngOpts :: !UnfoldingOpts

  , maxWorkerArgs :: Int

  , flushOut :: FlushOut

  , cslVersionFile :: Maybe FilePath

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
  , iniqueIncrement :: Int
  }

class HasDynFlags m where
  getDynFlags :: m DynFlags

class ContainsDynFlags t where
  extractDynFlags :: t -> DynFlags

type FatalMessager = String -> IO ()

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
  | RtsOptsSaftOnly
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

dopt :: DumpFlag -> DynFlags -> Bool
dopt = getDumpFlagFrom verbosity dumpFlags

gopt :: GeneralFlag -> DynFlags -> Bool
gopt Opt_PIC dflags
  | dynamicNow dflags = True
gopt Opt_ExternalDynamicRefs dflags
  | dynamicNow dflags = True
gopt Opt_SplitSections dflags
  | dynamicNow dflags = False
gopt f dflags = f `EnumSet.member` generalFlags dflags

wopt :: WarningFlag -> DynFlags -> Bool
wopt f dflags = f `EnumSet.member` warningFlags dflags

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
