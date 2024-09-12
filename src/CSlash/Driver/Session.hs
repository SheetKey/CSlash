module CSlash.Driver.Session
  ( DumpFlag(..)
  , GeneralFlag(..)
  , WarningFlag(..)
  , FatalMessager, FlushOut(..)
  , dopt
  , gopt
  , wopt
  , DynFlags(..)
  , HasDynFlags(..), ContainsDynFlags(..)
  , Option(..), showOpt

  , augmentByWorkingDirectory
  ) where 

import CSlash.Platform
import CSlash.Platform.Ways
-- import CSlash.Platform.Profile

import CSlash.Unit.Types
-- import CSlash.Unit.Parser
import CSlash.Unit.Module
import CSlash.Unit.Module.Warnings
import CSlash.Driver.DynFlags
import CSlash.Driver.Config.Diagnostic
import CSlash.Driver.Flags
import CSlash.Driver.Backend
import CSlash.Driver.Errors.Types
-- import GHC.Driver.Plugins.External
-- import GHC.Settings.Config
-- import GHC.Core.Unfold
-- import GHC.Driver.CmdLine
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
-- import GHC.Core.Opt.CallerCC

-- import GHC.SysTools.BaseDir ( expandToolDir, expandTopDir )

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

augmentByWorkingDirectory :: DynFlags -> FilePath -> FilePath
augmentByWorkingDirectory dflags fp | isRelative fp, Just offset <- workingDirectory dflags
  = offset </> fp
augmentByWorkingDirectory _ fp = fp
