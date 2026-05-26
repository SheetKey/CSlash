module CSlash.Iface.Make where

import CSlash.Cs

-- import GHC.Stg.InferTags.TagSig (StgCgInfos)
-- import GHC.StgToCmm.Types (CmmCgInfos (..))

import CSlash.Tc.Utils.TcType
import CSlash.Tc.Utils.Monad

-- import CSlash.Iface.Decl
import CSlash.Iface.Syntax
import CSlash.Iface.Recomp
import CSlash.Iface.Load
-- import GHC.Iface.Ext.Fields

-- import GHC.CoreToIface

-- import qualified GHC.LanguageExtensions as LangExt
import CSlash.Core
-- import GHC.Core.Class
-- import GHC.Core.Coercion.Axiom
import CSlash.Core.ConLike
-- import GHC.Core.InstEnv
-- import GHC.Core.FamInstEnv
import CSlash.Core.Ppr
-- import GHC.Core.RoughMap( RoughMatchTc(..) )

-- import GHC.Driver.Config.HsToCore.Usage
import CSlash.Driver.Env
import CSlash.Driver.Backend
import CSlash.Driver.DynFlags
-- import GHC.Driver.Plugins

import CSlash.Types.Var.Id
import CSlash.Types.Fixity.Env
-- import GHC.Types.SafeHaskell
-- import GHC.Types.Annotations
import CSlash.Types.Name
import CSlash.Types.Avail
import CSlash.Types.Name.Reader
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Types.Unique.DSet
import CSlash.Types.TypeEnv
import CSlash.Types.SourceFile
import CSlash.Types.TyThing
import CSlash.Types.PcInfo
import CSlash.Types.CompleteMatch
import CSlash.Types.SourceText
import CSlash.Types.SrcLoc ( unLoc )

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Logger

import CSlash.Data.FastString
import CSlash.Data.Maybe

-- import GHC.HsToCore.Docs
-- import GHC.HsToCore.Usage

import CSlash.Unit
import CSlash.Unit.Module.Warnings
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.ModDetails
import CSlash.Unit.Module.ModGuts
import CSlash.Unit.Module.ModSummary
import CSlash.Unit.Module.Deps

import Data.Function
import Data.List ( sortBy )
import Data.Ord
import Data.IORef

{- *********************************************************************
*                                                                      *
            Completing an interface
*                                                                      *
********************************************************************* -}

mkPartialIface
  :: CsEnv
  -> CoreProgram
  -> ModDetails
  -> ModSummary
  -> ModGuts
  -> PartialModIface
mkPartialIface cs_env core_prog mod_details mod_summary 
  ModGuts{ mg_module = this_mod
         , mg_cs_src = cs_src
         , mg_usages = usages
         , mg_deps = deps
         , mg_rdr_env = rdr_env
         , mg_fix_env = fix_env
         , mg_pc_info = pc_info
         }
  = mkIface_ cs_env this_mod core_prog cs_src deps rdr_env fix_env pc_info usages
    mod_summary mod_details

mkFullIface :: CsEnv -> PartialModIface -> Maybe a -> Maybe a -> IO ModIface
mkFullIface = panic "mkFullIface"

mkIface_
  :: CsEnv
  -> Module
  -> CoreProgram
  -> CsSource
  -> Dependencies
  -> GlobalRdrEnv
  -> NameEnv FixItem
  -> PcInfo
  -> [Usage]
  -> ModSummary
  -> ModDetails
  -> PartialModIface
mkIface_ cs_env this_mod core_prod cs_src deps rdr_env fix_env pc_info usages mod_summary
  ModDetails{ {-md_rules = rules -} md_types = type_env
            , md_exports = exports
            , md_complete_matches = complete_matches }
  = emptyPartialModIface this_mod -- MAJOR IFACE TODO  
