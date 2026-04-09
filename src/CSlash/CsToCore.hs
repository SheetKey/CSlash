module CSlash.CsToCore where

import CSlash.Driver.DynFlags
import CSlash.Driver.Config
import CSlash.Driver.Config.Core.Lint ( endPassCsEnvIO )
-- import GHC.Driver.Config.HsToCore.Ticks
-- import CSlash.Driver.Config.CsToCore.Usage
import CSlash.Driver.Env
import CSlash.Driver.Backend

import CSlash.Cs

import CSlash.CsToCore.Usage
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
import CSlash.Core as Core
-- import GHC.Core.FVs       ( exprsSomeFreeVarsList, exprFreeVars )
import CSlash.Core.SimpleOpt ( simpleOptPgm, simpleOptExpr )
import CSlash.Core.Utils
import CSlash.Core.Unfold.Make
-- import GHC.Core.Coercion
-- import GHC.Core.DataCon ( dataConWrapId )
import CSlash.Core.Make
import CSlash.Core.Opt.Pipeline.Types ( CoreToDo(..) )
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
import CSlash.Types.Var.Class
import CSlash.Types.Var.Id.Info
-- import GHC.Types.Id.Make ( mkRepPolyIdConcreteTyVars )
-- import GHC.Types.ForeignStubs
import CSlash.Types.Avail
import CSlash.Types.Basic
import CSlash.Types.Var.Set
import CSlash.Types.SrcLoc
import CSlash.Types.SourceFile
import CSlash.Types.TypeEnv
import CSlash.Types.Name hiding (varName)
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
        tcg_env@(TcGblEnv { tcg_mod = mod
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
  = let dflags = cs_dflags cs_env
        logger = cs_logger cs_env
        name_ppr_ctx = mkNamePprCtx (cs_unit_env cs_env) rdr_env
    in withTiming logger (text "Desugar" <+> brackets (ppr mod)) (const ()) $
       do let export_set = availsToNameSet exports
              bcknd = backend dflags

              ds_pc_info = emptyPcInfo other_pc_info

          (msgs, mb_res) <- initDs cs_env tcg_env $ do
            core_prs <- dsTopLCsBinds binds
            let pc_init | gopt Opt_Pc dflags = panic "pc_init"
                        | otherwise = panic "mempty"
            return (core_prs, pc_init)
            
          case mb_res of
            Nothing -> return (msgs, Nothing)
            Just (all_prs, ds_fords) -> do
              keep_alive <- readIORef keep_var
              let final_prs = addExportFlags bcknd export_set keep_alive (fromOL all_prs)

                  final_pgm = [Rec final_prs]

              endPassCsEnvIO cs_env name_ppr_ctx CoreDesugar final_pgm [] -- TODO: rules
              let simpl_opts = initSimpleOpts dflags
              let (ds_binds, occ_anald_binds) = simpleOptPgm simpl_opts mod final_pgm
              putDumpFileMaybe logger Opt_D_dump_occur_anal "Occurrence analysis"
                FormatCore (pprCoreBindings occ_anald_binds)

              endPassCsEnvIO cs_env name_ppr_ctx CoreDesugarOpt ds_binds [] -- TODO: rules

              let used_names = mkUsedNames tcg_env
                  home_unit = cs_home_unit cs_env
              let deps = mkDependencies home_unit
                                        (tcg_mod tcg_env)
                                        (tcg_imports tcg_env)

              let fc = cs_FC cs_env
              let unit_env = cs_unit_env cs_env
              usages <- initIfaceLoad cs_env $
                        mkUsageInfo fc unit_env mod (imp_mods imports) used_names merged

              let mod_guts = ModGuts
                    { mg_module = mod
                    , mg_cs_src = cs_src
                    , mg_loc = panic "mkFileSrcSpan mod_loc"
                    , mg_exports = exports
                    , mg_usages = usages
                    , mg_deps = deps
                    , mg_rdr_env = rdr_env
                    , mg_fix_env = fix_env
                    , mg_tcs = tcs
                    , mg_rules = [] -- TODO: fix if add tcg_rules/tcg_imp_specs
                    , mg_binds = ds_binds
                    , mg_pc_info = ds_pc_info
                    , mg_complete_matches = complete_matches
                    }

              return (msgs, Just mod_guts)

{- *********************************************************************
*                                                                      *
*              Add export flags to binders
*                                                                      *
********************************************************************* -}

addExportFlags :: Backend -> NameSet -> NameSet -> [(Id Zk, t)] -> [(Id Zk, t)]
addExportFlags bcknd exports keep_alive = mapFst add_export_flag
  where
    add_export_flag bndr
      | dont_discard bndr = setIdExported bndr
      | otherwise = bndr

    dont_discard :: Id Zk -> Bool
    dont_discard bndr = is_exported name
                        || name `elemNameSet` keep_alive
      where name = varName bndr

    is_exported :: Name -> Bool
    is_exported  | backendWantsGlobalBindings bcknd = isExternalName
                 | otherwise = (`elemNameSet` exports)
