module CSlash.CsToCore where

import CSlash.Driver.DynFlags
-- import CSlash.Driver.Config
-- import GHC.Driver.Config.Core.Lint ( endPassHscEnvIO )
-- import GHC.Driver.Config.HsToCore.Ticks
-- import GHC.Driver.Config.HsToCore.Usage
import CSlash.Driver.Env
import CSlash.Driver.Backend

import CSlash.Cs

-- import GHC.HsToCore.Usage
import CSlash.CsToCore.Monad
import CSlash.CsToCore.Errors.Types
import CSlash.CsToCore.Expr
import CSlash.CsToCore.Binds
-- import GHC.HsToCore.Foreign.Decl
-- import GHC.HsToCore.Ticks
-- import GHC.HsToCore.Breakpoints
-- import GHC.HsToCore.Coverage
-- import GHC.HsToCore.Docs

import CSlash.Tc.Types
-- import CSlash.Tc.Types.Origin ( Position(..) )
import CSlash.Tc.Utils.Monad  ( initIfaceLoad )

import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.Type.Compare( eqType )
import CSlash.Core.TyCon       ( tyConDataCons )
import CSlash.Core
-- import GHC.Core.FVs       ( exprsSomeFreeVarsList, exprFreeVars )
-- import GHC.Core.SimpleOpt ( simpleOptPgm, simpleOptExpr )
-- import GHC.Core.Utils
-- import GHC.Core.Unfold.Make
-- import GHC.Core.Coercion
-- import GHC.Core.DataCon ( dataConWrapId )
-- import GHC.Core.Make
-- import GHC.Core.Opt.Pipeline.Types ( CoreToDo(..) )
import CSlash.Core.Ppr

import CSlash.Builtin.Names
import CSlash.Builtin.Types.Prim
import CSlash.Builtin.Types

import CSlash.Data.Maybe    ( expectJust )
import CSlash.Data.OrdList
-- import GHC.Data.SizedSeq ( sizeSS )

import CSlash.Utils.Error
import CSlash.Utils.Outputable
import CSlash.Utils.Panic.Plain
import CSlash.Utils.Misc
import CSlash.Utils.Monad
import CSlash.Utils.Logger

import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
-- import GHC.Types.Id.Make ( mkRepPolyIdConcreteTyVars )
-- import GHC.Types.ForeignStubs
import CSlash.Types.Avail
import CSlash.Types.Basic
import CSlash.Types.Var.Set
import CSlash.Types.SrcLoc
import CSlash.Types.SourceFile
import CSlash.Types.TypeEnv
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Name.Env
import CSlash.Types.Name.Ppr
import CSlash.Types.PcInfo

import CSlash.Unit
import CSlash.Unit.Module.ModGuts
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.Deps

import Data.List (partition)
import Data.IORef
import Data.Traversable (for)

{- *********************************************************************
*                                                                      *
*              The main function: deSugar
*                                                                      *
********************************************************************* -}

deSugar :: CsEnv -> ModLocation -> TcGblEnv Zk -> IO (Messages DsMessage, Maybe ModGuts)
deSugar cs_env
        mod_loc
        tcg_env@(TcGblEnv { tcg_mod = id_mod
                          , tcg_src = cs_src
                          , tcg_type_env = type_env
                          , tcg_imports = imports
                          , tcg_exports = exports
                          , tcg_keep = keep_var
                          , tcg_rdr_env = rdr_env
                          , tcg_fix_env = fix_env
                          , tcg_merged = merged
                          , tcg_binds = binds
                          , tcg_tcs = tcs
                          , tcg_pc = other_pc_info
                          , tcg_complete_matches = complete_matches
                          })
  -- = let dflags = cs_dflags cs_env
  --       logger = cs_logger cs_env
  --       name_ppr_ctx = mkNamePprCtx (cs_unit_env cs_env) rdr_env
  --   in withTiming logger (text "Desugar" <+> brackets (ppr mod)) (const ()) $
  --      do let export_set = availsToNameSet exports
  --             bcknd = backend dflags

  --             ds_pc_info = emptyPcInfo other_pc_info

  --         (msgs, mb_res) <- initDs cs_env tcg_env $ do
  --           core_prs <- dsTopLCsBinds binds
  --           panic "post initDs"

  --         panic "deSugar unfinished"
  = panic "deSugar"
