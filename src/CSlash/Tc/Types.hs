module CSlash.Tc.Types
  ( module CSlash.Tc.Types
  , TcRef

  , TcGblEnv(..), TcLclEnv(..), TcLclCtxt(..)

  , ErrCtxt
  , ImportAvails(..)

  , TcTyKiEnv, TcBinderStack, TcBinder(..)
  , TcTyKiThing(..)
  ) where

import CSlash.Platform

import CSlash.Driver.Env
import CSlash.Driver.Env.KnotVars
-- import GHC.Driver.Config.Core.Lint
import CSlash.Driver.DynFlags
-- import {-# SOURCE #-} GHC.Driver.Hooks

import CSlash.Linker.Types

import CSlash.Cs

import CSlash.Tc.Utils.TcType
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Evidence
-- import GHC.Tc.Types.TH
import CSlash.Tc.Types.TcRef
import CSlash.Tc.Types.LclEnv
import CSlash.Tc.Types.BasicTypes
import CSlash.Tc.Types.ErrCtxt
-- import {-# SOURCE #-} GHC.Tc.Errors.Hole.Plugin ( HoleFitPlugin )
import CSlash.Tc.Errors.Types

-- import GHC.Core.Reduction ( Reduction(..) )
import CSlash.Core.Type
import CSlash.Core.TyCon  ( TyCon, AnyTyCon )
-- import GHC.Core.PatSyn ( PatSyn )
-- import GHC.Core.Lint   ( lintAxioms )
-- import GHC.Core.InstEnv
-- import GHC.Core.FamInstEnv
-- import GHC.Core.Predicate

import CSlash.Types.Fixity.Env
-- import GHC.Types.Annotations
import CSlash.Types.CompleteMatch
import CSlash.Types.Name.Reader
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Types.Avail
import CSlash.Types.Var
import CSlash.Types.TypeEnv
import CSlash.Types.SourceFile
import CSlash.Types.SrcLoc
import CSlash.Types.Unique.FM
import CSlash.Types.Basic
-- import GHC.Types.CostCentre.State
import CSlash.Types.PcInfo

import CSlash.Data.IOEnv
import CSlash.Data.Bag
import CSlash.Data.List.SetOps

import CSlash.Unit
import CSlash.Unit.Module.Warnings
import CSlash.Unit.Module.Deps
import CSlash.Unit.Module.ModDetails

import CSlash.Utils.Error
import CSlash.Utils.Outputable
import CSlash.Utils.Fingerprint
import CSlash.Utils.Panic
import CSlash.Utils.Logger

import CSlash.Builtin.Names ( isUnboundName )

-- import GHCi.Message
-- import GHCi.RemoteTypes

import Data.Set      ( Set )
import qualified Data.Set as S
import Data.Dynamic  ( Dynamic )
import Data.Map ( Map )
import Data.Typeable ( TypeRep )
import Data.Maybe    ( mapMaybe )

data NameShape = NameShape
  { ns_mod_name :: ModuleName
  , ns_exports :: [AvailInfo]
  , ns_map :: OccEnv Name
  }

{- *********************************************************************
*                                                                      *
               Standard monad definition for TcRn
*                                                                      *
********************************************************************* -}

type TcRnIf a b = IOEnv (Env a b)
type TcRn = TcRnIf TcGblEnv TcLclEnv

type IfM lcl = TcRnIf IfGblEnv lcl
type IfG = IfM ()
type IfL = IfM IfLclEnv

type RnM = TcRn

type TcM = TcRn

data Env gbl lcl = Env
  { env_top :: !CsEnv
  , env_ut :: {-# UNPACK #-} !Char
  , env_gbl :: gbl
  , env_lcl :: lcl
  }

instance ContainsDynFlags (Env gbl lcl) where
  extractDynFlags env = cs_dflags (env_top env)

instance ContainsLogger (Env gbl lcl) where
    extractLogger env = cs_logger (env_top env)

instance ContainsModule gbl => ContainsModule (Env gbl lcl) where
    extractModule env = extractModule (env_gbl env)

{- *********************************************************************
*                                                                      *
*                            RewriteEnv
*                     The rewriting environment
*                                                                      *
********************************************************************* -}

data RewriteEnv = RE
  { re_loc :: !CtLoc
  , re_flavor :: !CtFlavor
  , re_rewriters :: !(TcRef RewriterSet)
  }

{- *********************************************************************
*                                                                      *
                The interface environments
              Used when dealing with IfaceDecls
*                                                                      *
********************************************************************* -}  

data IfGblEnv = IfGblEnv
  { if_doc :: SDoc
  , if_rec_types :: (KnotVars (IfG TypeEnv))
  }

data IfLclEnv = IfLclEnv
  { if_mod :: !Module
  , if_loc :: SDoc
  , if_nsubst :: Maybe NameShape
  , if_implicits_env :: Maybe TypeEnv
  , if_tv_env :: FastStringEnv (TyVar KiVar)
  , if_id_env :: FastStringEnv (Id (TyVar KiVar) KiVar)
  }

{- *********************************************************************
*                                                                      *
                Global typechecker environment
*                                                                      *
********************************************************************* -}

data FrontendResult = FrontendTypecheck TcGblEnv

data TcGblEnv = TcGblEnv
  { tcg_mod :: Module
  , tcg_src :: CsSource
  , tcg_rdr_env :: GlobalRdrEnv
  , tcg_default :: Maybe [AnyType]
  , tcg_fix_env :: FixityEnv
  , tcg_type_env :: TypeEnv
  , tcg_type_env_var :: KnotVars (IORef TypeEnv)
  , tcg_exports :: [AvailInfo]
  , tcg_imports :: ImportAvails
  , tcg_dus :: DefUses
  , tcg_used_gres :: TcRef [GlobalRdrElt]
  , tcg_keep :: TcRef NameSet
  , tcg_dfun_n :: TcRef OccSet
  , tcg_merged :: [(Module, Fingerprint)]
  , tcg_rn_exports :: Maybe [(LIE Rn, Avails)]
  , tcg_rn_imports :: [LImportDecl Rn]
  , tcg_rn_decls :: Maybe (CsGroup Rn)
  , tcg_ki_ev_binds :: Bag KiEvBind
  , tcg_tr_module :: Maybe (Id (AnyTyVar AnyKiVar) AnyKiVar)
  , tcg_binds :: LCsBinds Tc
  , tcg_sigs :: NameSet
  , tcg_tcs :: [TyCon (TyVar KiVar) KiVar]
  , tcg_ksigs :: NameSet
  , tcg_hdr_info :: Maybe (XRec Rn ModuleName)
  , tcg_pc :: !AnyPcUsage
  , tcg_main :: Maybe Name
  , tcg_top_loc :: RealSrcSpan
  , tcg_static_wc :: TcRef WantedConstraints
  , tcg_complete_matches :: !CompleteMatches
  }

instance ContainsModule TcGblEnv where
  extractModule env = tcg_mod env

removeBindingShadowing :: HasOccName a => [a] -> [a]
removeBindingShadowing bindings = reverse $ fst $ foldl
  (\(bindingAcc, seenNames) binding ->
     if occName binding `elemOccSet` seenNames
     then (bindingAcc, seenNames)
     else (binding:bindingAcc, extendOccSet seenNames (occName binding)))
  ([], emptyOccSet) bindings

{- *********************************************************************
*                                                                      *
            Operations over ImportAvails
*                                                                      *
********************************************************************* -}

mkModDeps :: Set (UnitId, ModuleName) -> InstalledModuleEnv ModuleName
mkModDeps deps = S.foldl' add emptyInstalledModuleEnv deps
  where
    add env (uid, mod) = extendInstalledModuleEnv env (mkModule uid mod) mod

plusModDeps
  :: InstalledModuleEnv ModuleName
  -> InstalledModuleEnv ModuleName
  -> InstalledModuleEnv ModuleName 
plusModDeps = plusInstalledModuleEnv plus_mod_dep
  where
    plus_mod_dep m1 m2 = assertPpr (m1 == m2) (ppr m1 <+> ppr m2) m1

emptyImportAvails :: ImportAvails
emptyImportAvails = ImportAvails
                    { imp_mods = emptyModuleEnv
                    , imp_direct_dep_mods = emptyInstalledModuleEnv
                    , imp_dep_direct_pkgs = S.empty
                    }

plusImportAvails :: ImportAvails -> ImportAvails -> ImportAvails
plusImportAvails
  (ImportAvails { imp_mods = mods1
                , imp_direct_dep_mods = ddmods1
                , imp_dep_direct_pkgs = ddpkgs1 })
  (ImportAvails { imp_mods = mods2
                , imp_direct_dep_mods = ddmods2
                , imp_dep_direct_pkgs = ddpkgs2 })
  = ImportAvails { imp_mods = plusModuleEnv_C (++) mods1 mods2
                 , imp_direct_dep_mods = ddmods1 `plusModDeps` ddmods2
                 , imp_dep_direct_pkgs = ddpkgs1 `S.union` ddpkgs2 }
