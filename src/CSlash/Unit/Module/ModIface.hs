{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}

module CSlash.Unit.Module.ModIface
  ( ModIface
  , ModIface_
    ( mi_module
    , mi_cs_src
    , mi_deps
    , mi_usages
    , mi_exports
    , mi_fixities
    , mi_anns
    , mi_decls
    , mi_extra_decls
    , mi_globals
    , mi_pc
    , mi_complete_matches
    , mi_final_exts
    , mi_src_hash
    , mi_hi_bytes
    )
  , pattern ModIface
  , set_mi_module
  , set_mi_decls
  , set_mi_extra_decls
  , set_mi_anns
  , set_mi_fixities
  , set_mi_final_exts
  , set_mi_deps
  , set_mi_exports
  , IfaceBinHandle(..)
  , PartialModIface
  , ModIfaceBackend(..)
  , IfaceDeclExts
  , IfaceBackendExts
  , IfaceExport
  , mi_mn
  , mi_semantic_module
  , emptyPartialModIface
  , emptyFullModIface
  , mkIfaceHashCache
  , emptyIfaceHashCache
  ) where

import CSlash.Iface.Syntax
-- import GHC.Iface.Ext.Fields

import CSlash.Unit
import CSlash.Unit.Module.Deps
import CSlash.Unit.Module.Warnings

import CSlash.Types.Avail
import CSlash.Types.Fixity
import CSlash.Types.Fixity.Env
import CSlash.Types.PcInfo
import CSlash.Types.Name
import CSlash.Types.Name.Reader
-- import GHC.Types.SafeHaskell
import CSlash.Types.SourceFile
import CSlash.Types.Unique.DSet
import CSlash.Types.Unique.FM

import CSlash.Data.Maybe
import qualified CSlash.Data.Strict as Strict

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
  , mi_pc_hash :: !Fingerprint
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

data IfaceBinHandle (phase :: ModIfacePhase) where
  PartialIfaceBinHandle :: IfaceBinHandle 'ModIfaceCore
  FullIfaceBinHandle :: !(Strict.Maybe FullBinData) -> IfaceBinHandle 'ModIfaceFinal

data ModIface_ (phase :: ModIfacePhase) = PrivateModIface
  { mi_module_ :: !Module
  , mi_cs_src_ :: !CsSource
  , mi_deps_ :: Dependencies
  , mi_usages_ :: [Usage]
  , mi_exports_ :: ![IfaceExport]
  , mi_fixities_ :: [(OccName, Fixity)]
  , mi_anns_ :: [IfaceAnnotation]
  , mi_decls_ :: [IfaceDeclExts phase]
  , mi_extra_decls_ :: Maybe [IfaceBindingX IfaceMaybeRhs IfaceTopBndrInfo]
  , mi_globals_ :: !(Maybe IfGlobalRdrEnv)
  , mi_pc_ :: !AnyPcUsage
  , mi_complete_matches_ :: ![IfaceCompleteMatch]
  , mi_final_exts_ :: !(IfaceBackendExts phase)
  , mi_src_hash_ :: !Fingerprint
  , mi_hi_bytes_ :: !(IfaceBinHandle phase)
  }

mi_mn :: ModIface -> ModuleName
mi_mn = moduleName . mi_module_

mi_semantic_module :: ModIface_ a -> Module
mi_semantic_module = mi_module_

instance Binary ModIface where
  put_ bh (PrivateModIface { mi_final_exts_ = ModIfaceBackend {..}, .. }) = do
    put_ bh mi_module_
    put_ bh mi_cs_src_
    put_ bh mi_iface_hash
    put_ bh mi_mod_hash
    put_ bh mi_flag_hash
    put_ bh mi_opt_hash
    put_ bh mi_pc_hash
    lazyPut bh mi_deps_
    lazyPut bh mi_usages_
    put_ bh mi_exports_
    put_ bh mi_exp_hash
    put_ bh mi_fixities_
    lazyPut bh mi_anns_
    put_ bh mi_decls_
    put_ bh mi_extra_decls_
    put_ bh mi_pc_
    put_ bh mi_complete_matches_

  get bh = do
    mi_module_ <- get bh
    mi_cs_src_ <- get bh
    mi_iface_hash <- get bh
    mi_mod_hash <- get bh
    mi_flag_hash <- get bh
    mi_opt_hash <- get bh
    mi_pc_hash <- get bh
    mi_deps_ <- lazyGet bh
    mi_usages_ <- {-# SCC "bin_usages" #-} lazyGet bh
    mi_exports_ <- {-# SCC "bin_exports" #-} get bh
    mi_exp_hash <- get bh
    mi_fixities_ <- {-# SCC "bin_fixities" #-} get bh
    mi_anns_ <- {-# SCC "bin_anns" #-} lazyGet bh
    mi_decls_ <- {-# SCC "bin_tycldecls" #-} get bh
    mi_extra_decls_ <- get bh
    mi_pc_ <- get bh
    mi_complete_matches_ <- get bh
    return $ PrivateModIface
      { mi_src_hash_ = fingerprint0
      , mi_hi_bytes_ = FullIfaceBinHandle Strict.Nothing
      , mi_globals_ = Nothing
      , mi_final_exts_ = ModIfaceBackend
                        { mi_fix_fn = mkIfaceFixCache mi_fixities_
                        , mi_hash_fn = mkIfaceHashCache mi_decls_
                        , ..
                        }
      , ..
      }

type IfaceExport = AvailInfo

emptyPartialModIface :: Module -> PartialModIface
emptyPartialModIface mod = PrivateModIface
  { mi_module_ = mod
  , mi_cs_src_ = CsSrcFile
  , mi_src_hash_ = fingerprint0
  , mi_hi_bytes_ = PartialIfaceBinHandle
  , mi_deps_ = noDependencies
  , mi_usages_ = []
  , mi_exports_ = []
  , mi_fixities_ = []
  , mi_anns_ = []
  , mi_decls_ = []
  , mi_extra_decls_ = Nothing
  , mi_globals_ = Nothing
  , mi_pc_ = False
  , mi_complete_matches_ = []
  , mi_final_exts_ = ()
  }

emptyFullModIface :: Module -> ModIface
emptyFullModIface mod =
  (emptyPartialModIface mod)
  { mi_decls_ = []
  , mi_hi_bytes_ = FullIfaceBinHandle Strict.Nothing
  , mi_final_exts_ = ModIfaceBackend
    { mi_iface_hash = fingerprint0
    , mi_mod_hash = fingerprint0
    , mi_flag_hash = fingerprint0
    , mi_opt_hash = fingerprint0
    , mi_pc_hash = fingerprint0
    , mi_exp_hash = fingerprint0
    , mi_fix_fn = emptyIfaceFixCache
    , mi_hash_fn = emptyIfaceHashCache
    }
  }

mkIfaceHashCache :: [(Fingerprint, IfaceDecl)] -> OccName -> Maybe (OccName, Fingerprint)
mkIfaceHashCache pairs
  = \occ -> lookupOccEnv env occ
  where
    env = foldl' add_decl emptyOccEnv pairs
    add_decl env0 (v, d) = foldl' add env0 (ifaceDeclFingerprints v d)
      where
        add env0 (occ, hash) = extendOccEnv env0 occ (occ, hash)

emptyIfaceHashCache :: OccName -> Maybe (OccName, Fingerprint)
emptyIfaceHashCache _ = Nothing

set_mi_module :: Module -> ModIface_ phase -> ModIface_ phase
set_mi_module val iface = clear_mi_hi_bytes $ iface { mi_module_ = val }

set_mi_exports :: [IfaceExport] -> ModIface_ phase -> ModIface_ phase
set_mi_exports val iface = clear_mi_hi_bytes $ iface { mi_exports_ = val }

set_mi_decls :: [IfaceDeclExts phase] -> ModIface_ phase -> ModIface_ phase
set_mi_decls val iface = clear_mi_hi_bytes $ iface { mi_decls_ = val }

set_mi_extra_decls
  :: Maybe [IfaceBindingX IfaceMaybeRhs IfaceTopBndrInfo] -> ModIface_ phase -> ModIface_ phase
set_mi_extra_decls val iface = clear_mi_hi_bytes $ iface { mi_extra_decls_ = val }

set_mi_deps :: Dependencies -> ModIface_ phase -> ModIface_ phase
set_mi_deps val iface = clear_mi_hi_bytes $ iface { mi_deps_ = val }

set_mi_anns :: [IfaceAnnotation] -> ModIface_ phase -> ModIface_ phase
set_mi_anns val iface = clear_mi_hi_bytes $ iface { mi_anns_ = val }  

set_mi_final_exts :: IfaceBackendExts phase -> ModIface_ phase -> ModIface_ phase
set_mi_final_exts val iface = clear_mi_hi_bytes $ iface { mi_final_exts_ = val }

set_mi_fixities :: [(OccName, Fixity)] -> ModIface_ phase -> ModIface_ phase
set_mi_fixities val iface = clear_mi_hi_bytes $ iface { mi_fixities_ = val }

clear_mi_hi_bytes :: ModIface_ phase -> ModIface_ phase
clear_mi_hi_bytes iface = iface
  { mi_hi_bytes_ = case mi_hi_bytes_ iface of
      PartialIfaceBinHandle -> PartialIfaceBinHandle
      FullIfaceBinHandle _ -> FullIfaceBinHandle Strict.Nothing
  }

{-# INLINE ModIface #-}
{-# INLINE mi_module #-}
{-# INLINE mi_cs_src #-}
{-# INLINE mi_deps #-}
{-# INLINE mi_usages #-}
{-# INLINE mi_exports #-}
{-# INLINE mi_fixities #-}
{-# INLINE mi_anns #-}
{-# INLINE mi_decls #-}
{-# INLINE mi_extra_decls #-}
{-# INLINE mi_globals #-}
{-# INLINE mi_pc #-}
{-# INLINE mi_complete_matches #-}
{-# INLINE mi_final_exts #-}
{-# INLINE mi_src_hash #-}
{-# INLINE mi_hi_bytes #-}
{-# COMPLETE ModIface #-}

pattern ModIface ::
  Module -> CsSource -> Dependencies -> [Usage] ->
  [IfaceExport] -> [(OccName, Fixity)] -> 
  [IfaceAnnotation] -> [IfaceDeclExts phase] ->
  Maybe [IfaceBindingX IfaceMaybeRhs IfaceTopBndrInfo] -> 
  Maybe IfGlobalRdrEnv ->
  AnyPcUsage -> [IfaceCompleteMatch] -> 
  IfaceBackendExts phase -> Fingerprint -> IfaceBinHandle phase ->
  ModIface_ phase
pattern ModIface
  { mi_module
  , mi_cs_src
  , mi_deps
  , mi_usages
  , mi_exports
  , mi_fixities
  , mi_anns
  , mi_decls
  , mi_extra_decls
  , mi_globals
  , mi_pc
  , mi_complete_matches
  , mi_final_exts
  , mi_src_hash
  , mi_hi_bytes
  } <- PrivateModIface
    { mi_module_ = mi_module
    , mi_cs_src_ = mi_cs_src
    , mi_deps_ = mi_deps
    , mi_usages_ = mi_usages
    , mi_exports_ = mi_exports
    , mi_fixities_ = mi_fixities
    , mi_anns_ = mi_anns
    , mi_decls_ = mi_decls
    , mi_extra_decls_ = mi_extra_decls
    , mi_globals_ = mi_globals
    , mi_pc_ = mi_pc
    , mi_complete_matches_ = mi_complete_matches
    , mi_final_exts_ = mi_final_exts
    , mi_src_hash_ = mi_src_hash
    , mi_hi_bytes_ = mi_hi_bytes
    }
