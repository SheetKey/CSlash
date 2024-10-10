{-# LANGUAGE DeriveFunctor #-}

module CSlash.Iface.Recomp where

import CSlash.Data.FastString

import CSlash.Driver.Backend
import CSlash.Driver.Config.Finder
import CSlash.Driver.Env
import CSlash.Driver.DynFlags
import CSlash.Driver.Ppr
-- import GHC.Driver.Plugins

import CSlash.Iface.Syntax
import CSlash.Iface.Recomp.Binary
import CSlash.Iface.Load
-- import GHC.Iface.Recomp.Flags
-- import GHC.Iface.Env

import CSlash.Core
import CSlash.Tc.Utils.Monad
import CSlash.Cs

import CSlash.Data.Graph.Directed
import CSlash.Data.Maybe

import CSlash.Utils.Error
import CSlash.Utils.Panic
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Misc as Utils
import CSlash.Utils.Binary
import CSlash.Utils.Fingerprint
import CSlash.Utils.Exception
import CSlash.Utils.Logger
import CSlash.Utils.Constants (debugIsOn)

-- import GHC.Types.Annotations
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.SrcLoc
import CSlash.Types.Unique.Set
import CSlash.Types.Fixity.Env
import CSlash.Types.Unique.Map
import CSlash.Unit.External
import CSlash.Unit.Finder
import CSlash.Unit.State
import CSlash.Unit.Home
import CSlash.Unit.Module
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.ModSummary
import CSlash.Unit.Module.Warnings
import CSlash.Unit.Module.Deps

import Control.Monad
import Data.List (sortBy, sort, sortOn)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Word (Word64)
import Data.Either

--Qualified import so we can define a Semigroup instance
-- but it doesn't clash with Outputable.<>
import qualified Data.Semigroup
-- import GHC.List (uncons)
import Data.Ord
import Data.Containers.ListUtils
import Data.Bifunctor
import GHC.Iface.Errors.Ppr

data RecompileRequired
  = UpToDate
  | NeedsRecompile !CompileReason
  deriving Eq

data MaybeValidated a
  = UpToDateItem a
  | OutOfDateItem !CompileReason (Maybe a)
  deriving Functor

instance Outputable a => Outputable (MaybeValidated a) where
  ppr (UpToDateItem a) = text "UpToDate" <+> ppr a
  ppr (OutOfDateItem r _) = text "OutOfDate: " <+> ppr r

outOfDateItemBecause :: RecompReason -> Maybe a -> MaybeValidated a
outOfDateItemBecause reason item = OutOfDateItem (RecompBecause reason) item

data CompileReason
  = MustCompile
  | RecompBecause !RecompReason
  deriving Eq

instance Outputable CompileReason where
  ppr MustCompile = text "MustCompile"
  ppr (RecompBecause r) = text "RecompBecause" <+> ppr r

data RecompReason
  = UnitDepRemoved UnitId
  | ModulePackageChanged FastString
  | SourceFileChanged
  | ThisUnitIdChanged
  | HieMissing
  | HieOutdated
  | ModuleChanged ModuleName
  | ModuleRemoved (UnitId, ModuleName)
  | ModuleAdded (UnitId, ModuleName)
  | ModuleChangedRaw ModuleName
  | ModuleChangedIface ModuleName
  | FileChanged FilePath
  | CustomReason String
  | FlagsChanged
  | OptimFlagsChange
  | PcFlagsChanged
  | MissingObjectFile
  | MissingDynObjectFile
  | MissingDynHiFile
  | MismatchedDynHiFile
  | ObjectsChange
  | LibraryChanged
  deriving Eq

instance Outputable RecompReason where
  ppr rr = case rr of
    UnitDepRemoved uid -> ppr uid <+> text "removed"
    ModulePackageChanged s -> ftext s <+> text "package changed"
    SourceFileChanged -> text "Source file changed"
    ThisUnitIdChanged -> text "-this-unit-id changed"
    HieMissing -> text "HIE file is missing"
    HieOutdated -> text "HIE file is out of date"
    ModuleChanged m -> ppr m <+> text "changed"
    ModuleRemoved (_, m) -> ppr m <+> text "removed"
    ModuleAdded(_, m) -> ppr m <+> text "added"
    ModuleChangedRaw m -> ppr m <+> text "changed (raw)"
    ModuleChangedIface m -> ppr m <+> text "changed (interface)"
    FileChanged fp -> text fp <+> text "changed"
    CustomReason s -> text s
    FlagsChanged -> text "Flags changed"
    OptimFlagsChange -> text "Optimisation flags changed"
    PcFlagsChanged -> text "PC flags changed"
    MissingObjectFile -> text "Missing object file"
    MissingDynObjectFile -> text "Missing dynamic object file"
    MissingDynHiFile -> text "Missing dynamic interface file"
    MismatchedDynHiFile -> text "Mismatched dynamic interface file"
    ObjectsChange -> text "Objects changed"
    LibraryChanged -> text "Library changed"

checkOldIface :: CsEnv -> ModSummary -> Maybe ModIface -> IO (MaybeValidated ModIface)
checkOldIface cs_env mod_summary maybe_iface = do
  let dflags = cs_dflags cs_env
      logger = cs_logger cs_env
  showPass logger $
    "Checking old interface for "
    ++ (showPpr dflags $ ms_mod mod_summary)
    ++ " (use -ddump-hi-diffs for more details)"
  initIfaceCheck (text "checkOldIface") cs_env $
    check_old_iface cs_env mod_summary maybe_iface

check_old_iface :: CsEnv -> ModSummary -> Maybe ModIface -> IfG (MaybeValidated ModIface)
check_old_iface cs_env mod_summary maybe_iface = panic "check_old_iface"
