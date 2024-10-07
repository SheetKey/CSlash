module CSlash.Unit.Module.ModGuts where

-- import GHC.ByteCode.Types
-- import GHC.ForeignSrcLang

import CSlash.Cs

import CSlash.Unit
import CSlash.Unit.Module.Deps
import CSlash.Unit.Module.Warnings

-- import GHC.Core.InstEnv ( InstEnv, ClsInst )
-- import GHC.Core.FamInstEnv
import CSlash.Core         ( CoreProgram{-, CoreRule-} )
import CSlash.Core.TyCon
-- import GHC.Core.PatSyn

import CSlash.Linker.Types ( SptEntry(..) )

-- import GHC.Types.Annotations ( Annotation )
import CSlash.Types.Avail
import CSlash.Types.CompleteMatch
import CSlash.Types.Fixity.Env
-- import GHC.Types.ForeignStubs
import CSlash.Types.PcInfo
import CSlash.Types.Name.Reader
import CSlash.Types.Name.Set (NameSet)
-- import GHC.Types.SafeHaskell
import CSlash.Types.SourceFile ( CsSource(..){-, hscSourceToIsBoot-} )
import CSlash.Types.SrcLoc
-- import GHC.Types.CostCentre

import Data.Set (Set)

data CgGuts = CgGuts
  { cg_module :: !Module
  , cg_tycons :: [TyCon]
  , cg_binds :: CoreProgram
  --, cg_ccs :: [CostCentre]
  --, cg_foreign :: !ForeignStubs
  --, cg_foreign_files :: ![(ForeignSrcLang, FilePath)]
  , cg_dep_pkgs :: !(Set UnitId)
  , cg_pc_info :: !PcInfo
  , cg_spt :: [SptEntry]
  }
