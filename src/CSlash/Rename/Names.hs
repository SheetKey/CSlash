module CSlash.Rename.Names where

import CSlash.Driver.Env
import CSlash.Driver.Session
-- import GHC.Driver.Ppr

-- import GHC.Rename.Env
-- import GHC.Rename.Fixity
-- import GHC.Rename.Utils ( warnUnusedTopBinds )
-- import GHC.Rename.Unbound
-- import qualified GHC.Rename.Unbound as Unbound

-- import GHC.Tc.Errors.Types
-- import GHC.Tc.Utils.Env
-- import GHC.Tc.Utils.Monad
-- import GHC.Tc.Types.LclEnv
-- import GHC.Tc.Zonk.TcType ( tcInitTidyEnv )

import CSlash.Cs
-- import CSlash.Iface.Load   ( loadSrcInterface )
-- import CSlash.Iface.Syntax ( fromIfaceWarnings )
import CSlash.Builtin.Names
-- import CSlash.Parser.PostProcess ( setRdrNameSpace )
import CSlash.Core.Type
-- import GHC.Core.PatSyn
import CSlash.Core.TyCon ( TyCon, tyConName )
-- import qualified GHC.LanguageExtensions as LangExt

import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Misc as Utils
import CSlash.Utils.Panic

import CSlash.Types.Fixity.Env
-- import GHC.Types.SafeHaskell
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Types.Name.Reader
import CSlash.Types.Avail
-- import GHC.Types.FieldLabel
import CSlash.Types.Hint
import CSlash.Types.SourceFile
import CSlash.Types.SrcLoc as SrcLoc
import CSlash.Types.Basic  ( TopLevelFlag(..) )
import CSlash.Types.SourceText
import CSlash.Types.Id
import CSlash.Types.PcInfo
import CSlash.Types.PkgQual
import CSlash.Types.GREInfo (ConInfo(..))

import CSlash.Unit
import CSlash.Unit.Module.Warnings
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.Imported
import CSlash.Unit.Module.Deps
import CSlash.Unit.Env

import CSlash.Data.Bag
import CSlash.Data.FastString
import CSlash.Data.FastString.Env
import CSlash.Data.Maybe
import CSlash.Data.List.SetOps ( removeDups )

import Control.Monad
import Data.Foldable    ( for_ )
import Data.IntMap      ( IntMap )
import qualified Data.IntMap as IntMap
import Data.Map         ( Map )
import qualified Data.Map as Map
import Data.Ord         ( comparing )
import Data.List        ( partition, find, sortBy )
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NE
import Data.Function    ( on )
import qualified Data.Set as S
import System.FilePath  ((</>))
import System.IO

renameRawPkgQual :: UnitEnv -> ModuleName -> RawPkgQual -> PkgQual
renameRawPkgQual _ _ NoRawPkgQual = NoRawPkgQual
renameRawPkgQual _ _ (RawPkgQual _) = panic "renameRawPkgQual RawPkgQual"
