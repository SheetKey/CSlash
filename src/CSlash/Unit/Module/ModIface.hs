{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE RecordWildCards #-}
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
import CSlash.Types.PcInfo
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
  , mi_pc :: !AnyPcUsage
  , mi_complete_matches :: ![IfaceCompleteMatch]
  , mi_final_exts :: !(IfaceBackendExts phase)
  , mi_src_hash :: !Fingerprint
  }

mi_mn :: ModIface -> ModuleName
mi_mn = moduleName . mi_module 

mi_semantic_module :: ModIface_ a -> Module
mi_semantic_module = mi_module

instance Binary ModIface where
  put_ bh (ModIface { mi_final_exts = ModIfaceBackend {..}, .. }) = do
    put_ bh mi_module
    put_ bh mi_cs_src
    put_ bh mi_iface_hash
    put_ bh mi_mod_hash
    put_ bh mi_flag_hash
    put_ bh mi_opt_hash
    put_ bh mi_pc_hash
    lazyPut bh mi_deps
    lazyPut bh mi_usages
    put_ bh mi_exports
    put_ bh mi_exp_hash
    put_ bh mi_fixities
    lazyPut bh mi_anns
    put_ bh mi_decls
    put_ bh mi_extra_decls
    put_ bh mi_pc
    put_ bh mi_complete_matches

  get bh = do
    mi_module <- get bh
    mi_cs_src <- get bh
    mi_iface_hash <- get bh
    mi_mod_hash <- get bh
    mi_flag_hash <- get bh
    mi_opt_hash <- get bh
    mi_pc_hash <- get bh
    mi_deps <- lazyGet bh
    mi_usages <- {-# SCC "bin_usages" #-} lazyGet bh
    mi_exports <- {-# SCC "bin_exports" #-} get bh
    mi_exp_hash <- get bh
    mi_fixities <- {-# SCC "bin_fixities" #-} get bh
    mi_anns <- {-# SCC "bin_anns" #-} lazyGet bh
    mi_decls <- {-# SCC "bin_tycldecls" #-} get bh
    mi_extra_decls <- get bh
    mi_pc <- get bh
    mi_complete_matches <- get bh
    return $ ModIface
      { mi_src_hash = fingerprint0
      , mi_globals = Nothing
      , mi_final_exts = ModIfaceBackend
                        { mi_fix_fn = mkIfaceFixCache mi_fixities
                        , mi_hash_fn = mkIfaceHashCache mi_decls
                        , ..
                        }
      , ..
      }

type IfaceExport = AvailInfo

emptyPartialModIface :: Module -> PartialModIface
emptyPartialModIface mod = ModIface
  { mi_module = mod
  , mi_cs_src = CsSrcFile
  , mi_src_hash = fingerprint0
  , mi_deps = noDependencies
  , mi_usages = []
  , mi_exports = []
  , mi_fixities = []
  , mi_anns = []
  , mi_decls = []
  , mi_extra_decls = Nothing
  , mi_globals = Nothing
  , mi_pc = False
  , mi_complete_matches = []
  , mi_final_exts = ()
  }

emptyFullModIface :: Module -> ModIface
emptyFullModIface mod =
  (emptyPartialModIface mod)
  { mi_decls = []
  , mi_final_exts = ModIfaceBackend
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
