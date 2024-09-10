{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module CSlash.Unit.Module.ModIface where

import CSlash.Iface.Syntax
-- import GHC.Iface.Ext.Fields

import CSlash.Unit
import CSlash.Unit.Module.Deps
import CSlash.Unit.Module.Warnings

import CSlash.Types.Avail
import CSlash.Types.Fixity
import CSlash.Types.Fixity.Env
-- import GHC.Types.HpcInfo
import CSlash.Types.Name
import CSlash.Types.Name.Reader
-- import GHC.Types.SafeHaskell
import CSlash.Types.SourceFile
import CSlash.Types.Unique.DSet
import CSlash.Types.Unique.FM

import CSlash.Data.Maybe

import CSlash.Utils.Fingerprint
import CSlash.Utils.Binary

import Control.DeepSeq
import Control.Exception

type PartialModIface = ModIface_ 'ModIfaceCore

type ModIface = ModIface_ 'ModIfaceFinal

data ModIfaceBackend = ModIfaceBackend
  { mi_iface_hash :: !Fingerprint
  , mi_mod_hash :: !Fingerprint
  , mi_flag_hash :: !Fingerprint
  , mi_opt_hash :: !Fingerprint
  , mi_hpc_hash :: !Fingerprint
  , mi_exp_hash :: !Fingerprint
  , mi_fix_fn :: !(OccName -> Maybe Fixity)
  , mi_hash_fn :: !(OccName -> Maybe (OccName, Fingerprint))
  }

data ModIfacePhase
  = ModIfaceCore
  | ModIfaceFinal

type family IfaceDeclExts (phase :: ModIfacePhase) = decl | decl -> phase where
  IfaceDeclExts 'ModIfaceCore = IfaceDecl
  IfaceDeclExts 'ModIfaceFinal = (Fingerprint, IfaceDecl)

type family IfaceBackendExts (phase :: ModIfacePhase) = bk | bk -> phase where
  IfaceBackendExts 'ModIfaceCore = ()
  IfaceBackendExts 'ModIfaceFinal = ModIfaceBackend

data ModIface_ (phase :: ModIfacePhase) = ModIface
  { mi_module :: !Module
  , mi_cs_src :: !CsSource
  , mi_deps :: Dependencies
  , mi_usages :: [Usage]
  , mi_exports :: ![IfaceExport]
  , mi_fixities :: [(OccName, Fixity)]
  , mi_anns :: [IfaceAnnotation]
  , mi_decls :: [IfaceDeclExts phase]
  , mi_extra_decls :: Maybe [IfaceBindingX IfaceMaybeRhs IfaceTopBndrInfo]
  , mi_globals :: !(Maybe IfGlobalRdrEnv)
  -- , mi_hpc :: !AnyHpcUsage
  , mi_complete_matches :: ![IfaceCompleteMatch]
  , mi_final_exts :: !(IfaceBackendExts phase)
  -- , mi_ext_fields :: !ExtensibleFields
  , mi_src_hash :: !Fingerprint
  }

type IfaceExport = AvailInfo
