module CSlash.Driver.DynFlags where

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
-- import GHC.Utils.CliOption
-- import GHC.SysTools.Terminal ( stderrSupportsAnsiColors )
-- import GHC.UniqueSubdir (uniqueSubdir)
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.TmpFs

-- import qualified GHC.Types.FieldLabel as FieldLabel
import qualified CSlash.Utils.Ppr.Colour as Col
import qualified CSlash.Data.EnumSet as EnumSet

import CSlash.Core.Opt.CallerCC.Types

import Control.Monad (msum, (<=<))
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (ExceptT)
import Control.Monad.Trans.Reader (ReaderT)
import Control.Monad.Trans.Writer (WriterT)
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
  { cslMode :: CslMode
  , cslLink :: CslLink
  , backend :: !Backend

  , cslNameVersion :: {-# UNPACK #-} !CslNameVersion
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

newtype FlushOut = FlushOut (IO ())

defaultFlushOut :: FlushOut
defaultFlushOut = FlushOut $ hFlush stdout

data ParMakeCount
  = ParMakeThisMany Int
  | ParMakeNumProcessors
  | ParMakeSemaphore FilePath

data CslMode
  = CompManager
  | OneShot
  | MkDepend
  deriving Eq

instance Outputable CslMode where
  ppr CompManager = text "CompManager"
  ppr OneShot = text "OneShot"
  ppr MkDepend = text "MkDepend"

data CslLink
  = NoLink
  | LinkBinary
  | LinkInMemory
  | LinkDynLib
  | LinkStaticLib
  | LinkMergedObj
  deriving (Eq, Show)

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

wopt :: WarningFlag -> DynFlag -> Bool
wopt f dflags = f `EnumSet.member` warningFlags dflags
