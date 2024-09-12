module CSlash.Driver.Make where

import CSlash.Platform

-- import GHC.Tc.Utils.Backpack
-- import GHC.Tc.Utils.Monad  ( initIfaceCheck, concatMapM )

-- import GHC.Runtime.Interpreter
-- import qualified GHC.Linker.Loader as Linker
import CSlash.Linker.Types

import CSlash.Platform.Ways

-- import GHC.Driver.Config.Finder (initFinderOpts)
import CSlash.Driver.Config.Parser (initParserOpts)
import CSlash.Driver.Config.Diagnostic
import CSlash.Driver.Phases
-- import GHC.Driver.Pipeline
import CSlash.Driver.Session
import CSlash.Driver.Backend
import CSlash.Driver.Monad
import CSlash.Driver.Env
import CSlash.Driver.Errors
import CSlash.Driver.Errors.Types
import CSlash.Driver.Main
-- import GHC.Driver.MakeSem

-- import GHC.Parser.Header

-- import GHC.Iface.Load      ( cannotFindModule )
-- import GHC.IfaceToCore     ( typecheckIface )
-- import GHC.Iface.Recomp    ( RecompileRequired(..), CompileReason(..) )

import CSlash.Data.Bag        ( listToBag )
import CSlash.Data.Graph.Directed
import CSlash.Data.FastString
import CSlash.Data.Maybe      ( expectJust )
import CSlash.Data.StringBuffer
-- import qualified GHC.LanguageExtensions as LangExt

import CSlash.Utils.Exception ( throwIO, SomeAsyncException )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc
import CSlash.Utils.Error
import CSlash.Utils.Logger
import CSlash.Utils.Fingerprint
import CSlash.Utils.TmpFs

import CSlash.Types.Basic
import CSlash.Types.Error
import CSlash.Types.Target
import CSlash.Types.SourceFile
import CSlash.Types.SourceError
import CSlash.Types.SrcLoc
import CSlash.Types.Unique.Map
import CSlash.Types.PkgQual

import CSlash.Unit
import CSlash.Unit.Env
-- import GHC.Unit.Finder
import CSlash.Unit.Module.ModSummary
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.Graph
import CSlash.Unit.Home.ModInfo
import CSlash.Unit.Module.ModDetails

import Data.Either ( rights, partitionEithers, lefts )
import qualified Data.Map as Map
import qualified Data.Set as Set

import Control.Concurrent ( newQSem, waitQSem, signalQSem, ThreadId, killThread, forkIOWithUnmask )
import qualified GHC.Conc as CC
import Control.Concurrent.MVar
import Control.Monad
import Control.Monad.Trans.Except ( ExceptT(..), runExceptT, throwE )
import qualified Control.Monad.Catch as MC
import Data.IORef
import Data.Maybe
import Data.Time
import Data.List (sortOn)
import Data.Bifunctor (first)
import System.Directory
import System.FilePath
import System.IO        ( fixIO )

import GHC.Conc ( getNumProcessors, getNumCapabilities, setNumCapabilities )
import Control.Monad.IO.Class
import Control.Monad.Trans.Reader
-- import GHC.Driver.Pipeline.LogQueue
import qualified Data.Map.Strict as M
import CSlash.Types.TypeEnv
import Control.Monad.Trans.State.Lazy
import Control.Monad.Trans.Class
import CSlash.Driver.Env.KnotVars
import Control.Concurrent.STM
import Control.Monad.Trans.Maybe
-- import GHC.Runtime.Loader
-- import GHC.Rename.Names
import CSlash.Utils.Constants
import CSlash.Types.Unique.DFM (udfmRestrictKeysSet)
import CSlash.Types.Unique
-- import CSlash.Iface.Errors.Types

import qualified CSlash.Data.Word64Set as W

-- -----------------------------------------------------------------------------
-- Loading the program

data LoadHowMuch
  = LoadAllTargets
  | LoadUpTo HomeUnitModule
  | LoadDependenciesOf HomeUnitModule
