{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Iface.Load where

import CSlash.Platform.Profile

import Prelude hiding ((<>))

-- import {-# SOURCE #-} GHC.IfaceToCore
--    ( tcIfaceDecls, tcIfaceRules, tcIfaceInst, tcIfaceFamInst
--    , tcIfaceAnnotations, tcIfaceCompleteMatches )

import CSlash.Driver.Config.Finder
import CSlash.Driver.Env
import CSlash.Driver.Errors.Types
import CSlash.Driver.DynFlags
-- import GHC.Driver.Hooks
-- import GHC.Driver.Plugins

import CSlash.Iface.Syntax
-- import GHC.Iface.Ext.Fields
import CSlash.Iface.Binary
-- import GHC.Iface.Rename
import CSlash.Iface.Env
import CSlash.Iface.Errors as Iface_Errors

import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad

import CSlash.Utils.Binary   ( BinData(..) )
import CSlash.Utils.Error
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Logger

import CSlash.Settings.Constants

import CSlash.Builtin.Names
import CSlash.Builtin.Utils
-- import GHC.Builtin.PrimOps    ( allThePrimOps, primOpFixity, primOpOcc )

-- import GHC.Core.Rules
import CSlash.Core.TyCon
-- import GHC.Core.InstEnv
-- import GHC.Core.FamInstEnv

-- import CSlash.Types.Id.Make      ( seqId )
-- import GHC.Types.Annotations
import CSlash.Types.Name
import CSlash.Types.Name.Cache
import CSlash.Types.Name.Env
import CSlash.Types.Avail
import CSlash.Types.Fixity
import CSlash.Types.Fixity.Env
import CSlash.Types.SourceError
import CSlash.Types.SourceText
import CSlash.Types.SourceFile
-- import GHC.Types.SafeHaskell
import CSlash.Types.TypeEnv
import CSlash.Types.Unique.DSet
import CSlash.Types.SrcLoc
import CSlash.Types.TyThing
import CSlash.Types.PkgQual

import CSlash.Unit.External
import CSlash.Unit.Module
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.Deps
import CSlash.Unit.State
import CSlash.Unit.Home
import CSlash.Unit.Home.ModInfo
import CSlash.Unit.Finder
import CSlash.Unit.Env

import CSlash.Data.Maybe

import Control.Monad
import Data.Map ( toList )
import System.FilePath
import System.Directory
import CSlash.Driver.Env.KnotVars
import CSlash.Iface.Errors.Types

import Debug.Trace (trace)

{- *********************************************************************
*                                                                      *
        loadSrcInterface, loadOrphanModules, loadInterfaceForName

                These three are called from TcM-land
*                                                                      *
********************************************************************* -}

loadSrcInterface :: SDoc -> ModuleName -> PkgQual -> RnM ModIface
loadSrcInterface doc mod maybe_pkg = do
  res <- loadSrcInterface_maybe doc mod maybe_pkg
  case res of
    Failed err -> failWithTc $ TcRnInterfaceError $ Can'tFindInterface err $ LookingForModule mod
    Succeeded iface -> return iface

loadSrcInterface_maybe
  :: SDoc -> ModuleName -> PkgQual -> RnM (MaybeErr MissingInterfaceError ModIface)
loadSrcInterface_maybe doc mod maybe_pkg = do
  cs_env <- getTopEnv
  res <- liftIO $ findImportedModule cs_env mod maybe_pkg
  case res of
    Found _ mod -> initIfaceTcRn $ loadInterface doc mod ImportByUser
    err -> return $ Failed $ cannotFindModule cs_env mod err

{- *********************************************************************
*                                                                      *
                loadInterface

        The main function to load an interface
        for an imported module, and put it in
        the External Package State
*                                                                      *
********************************************************************* -}

loadInterface :: SDoc -> Module -> WhereFrom -> IfM lcl (MaybeErr MissingInterfaceError ModIface)
loadInterface doc_str mod from
  | isHoleModule mod
  = do cs_env <- getTopEnv
       let home_unit = cs_home_unit cs_env
       loadInterface doc_str (mkHomeModule home_unit (moduleName mod)) from
  | otherwise
  = do logger <- getLogger
       withTimingSilent logger (text "loading interface") (pure ()) $ do
         (eps, hug) <- getEpsAndHug
         gbl_env <- getGblEnv

         liftIO $ trace_if logger (text "Considering whether to load" <+> ppr mod <+> ppr from)

         cs_env <- getTopEnv
         let mhome_unit = ue_homeUnit (cs_unit_env cs_env)
         case lookupIfaceByModule hug (eps_PIT eps) mod of
           Just iface -> return (Succeeded iface)
           _ -> do read_result <- liftIO $ computeInterface cs_env doc_str mod
                   case read_result of
                     Failed err -> do let fake_iface = emptyFullModIface mod
                                      updateEps_ $ \eps -> eps
                                        { eps_PIT = extendModuleEnv (eps_PIT eps)
                                                                    (mi_module fake_iface)
                                                                    fake_iface }
                                      return (Failed err)
                     Succeeded (iface, loc) ->
                       let loc_doc = text loc
                       in initIfaceLcl (mi_semantic_module iface) loc_doc $
                          dontLeakTheHUG $ do
                            massertPpr ((isOneShot (csMode (cs_dflags cs_env)))
                                        || moduleUnitId mod `notElem` cs_all_home_unit_ids cs_env
                                        || mod == cSLASH_PRIM)
                              (text "Attempting to load home package interface into the EPS"
                               $$ ppr hug $$ doc_str $$ ppr mod $$ ppr (moduleUnitId mod))
                            ignore_prags <- goptM Opt_IgnoreInterfacePragmas
                            new_eps_decls <- panic "tcIfaceDecls"
                              -- tcIfaceDecls ignore_prags (mi_decls iface)
                            new_eps_complete_matches <- panic "tcIfaceCompleteMatches"
                              -- tcIfaceCompleteMatches (mi_complete_matches iface)
                            let final_iface = iface
                                  { mi_decls = panic "No mi_decls in PIT" }
                            updateEps_ $ \eps ->
                              if elemModuleEnv mod (eps_PIT eps)
                              then eps
                              else eps
                                   { eps_PIT = extendModuleEnv (eps_PIT eps) mod final_iface
                                   , eps_PTE = addDeclsToPTE (eps_PTE eps) new_eps_decls
                                   , eps_complete_matches = eps_complete_matches eps
                                                            ++ new_eps_complete_matches
                                   , eps_stats = addEpsInStats (eps_stats eps)
                                                               (length new_eps_decls)
                                   }
                            return (Succeeded iface)

dontLeakTheHUG :: IfL a -> IfL a
dontLeakTheHUG thing_inside = do
  env <- getTopEnv
  let inOneShot = isOneShot (csMode (cs_dflags env))
      cleanGblEnv gbl_env
        | inOneShot = gbl_env
        | otherwise = gbl_env { if_rec_types = emptyKnotVars }
      cleanTopEnv cs_env = let !maybe_type_vars | inOneShot = Just (cs_type_env_vars env)
                                                | otherwise = Nothing
                               old_unit_env = cs_unit_env cs_env
                               keepForBackpack hmi
                                 | isHoleModule (mi_semantic_module (hm_iface hmi)) = True
                                 | otherwise = False
                               pruneHomeUnitEnv hme = hme
                                 { homeUnitEnv_hpt = emptyHomePackageTable }
                               !unit_env = old_unit_env
                                 { ue_home_unit_graph =
                                     if anyHpt keepForBackpack (ue_hpt old_unit_env)
                                     then ue_home_unit_graph old_unit_env
                                     else unitEnv_map pruneHomeUnitEnv
                                                      (ue_home_unit_graph old_unit_env)
                                 }
                           in cs_env
                              { cs_targets = panic "cleanTopEnv: cs_targets"
                              , cs_mod_graph = panic "cleanTopEnv: cs_mod_graph"
                              , cs_type_env_vars = case maybe_type_vars of
                                  Just vars -> vars
                                  Nothing -> panic "cleanTopEnv: cs_type_env_vars"
                              , cs_unit_env = unit_env
                              }
  updTopEnv cleanTopEnv $ updGblEnv cleanGblEnv $ do
    !_ <- getTopEnv
    !_ <- getGblEnv
    thing_inside

computeInterface
  :: CsEnv -> SDoc -> Module -> IO (MaybeErr MissingInterfaceError (ModIface, FilePath))
computeInterface cs_env doc_str mod0 = do
  massert (not (isHoleModule mod0))
  let mhome_unit = cs_home_unit_maybe cs_env
      find_iface m = findAndReadIface cs_env doc_str m mod0
  case getModuleInstantiation mod0 of
    (imod, Just indef)
      | Just home_unit <- mhome_unit
      , isHomeUnitIndefinite home_unit
        -> find_iface imod
           >>= \case Succeeded (iface0, path) ->
                       rnModIface cs_env (instUnitInsts (moduleUnit indef)) Nothing  iface0
                       >>= \case Right x -> return (Succeeded (x, path))
                                 Left errs -> throwErrors (CsTcRnMessage <$> errs)
                     Failed err -> return (Failed err)
    (mod, _) -> find_iface mod

rnModIface _ _ _ iface = trace "rnModIface" $ return $ Right iface

addDeclsToPTE :: PackageTypeEnv -> [(Name, TyThing)] -> PackageTypeEnv
addDeclsToPTE pte things = extendNameEnvList pte things

{- *********************************************************************
*                                                                      *
            Reading an interface file
*                                                                      *
********************************************************************* -}

findAndReadIface
  :: CsEnv
  -> SDoc
  -> InstalledModule
  -> Module
  -> IO (MaybeErr MissingInterfaceError (ModIface, FilePath))
findAndReadIface  cs_env doc_str mod wanted_mod = do
  let profile = targetProfile dflags
      unit_state = cs_units cs_env
      fc = cs_FC cs_env
      name_cache = cs_NC cs_env
      mhome_unit = cs_home_unit_maybe cs_env
      dflags = cs_dflags cs_env
      logger = cs_logger cs_env
      other_fopts = initFinderOpts . homeUnitEnv_dflags <$> (cs_HUG cs_env)

  trace_if logger $sep [ hsep [ text "Reading interface for"
                              , ppr mod <> semi ]
                       , nest 4 (text "reason:" <+> doc_str) ]

  if mod `installedModuleEq` cSLASH_PRIM
    then return (Succeeded (cslPrimIface, "<built in interface for CSL.Prim>"))
    else do let fopts = initFinderOpts dflags
            mb_found <- liftIO (findExactModule fc fopts other_fopts unit_state mhome_unit mod)
            case mb_found of
              InstalledFound loc mod ->
                case mhome_unit of
                  Just home_unit
                    | isHomeInstalledModule home_unit mod
                    , not (isOneShot (csMode dflags))
                      -> return (Failed (HomeModError mod loc))
                  _ -> do r <- read_file
                            logger name_cache unit_state dflags wanted_mod (ml_hi_file loc)
                          case r of
                            Failed err -> return $ Failed $ BadIfaceFile err
                            Succeeded (iface, fp) -> do
                              r2 <- load_dynamic_too_maybe logger name_cache unit_state
                                    (setDynamicNow dflags) wanted_mod iface loc
                              case r2 of
                                Failed sdoc -> return $ Failed sdoc
                                Succeeded {} -> return $ Succeeded (iface, fp)
              err -> do trace_if logger (text "...not found")
                        return $ Failed $ cannotFindInterface unit_state mhome_unit
                                          profile (moduleName mod) err

load_dynamic_too_maybe
  :: Logger
  -> NameCache
  -> UnitState
  -> DynFlags
  -> Module
  -> ModIface
  -> ModLocation
  -> IO (MaybeErr MissingInterfaceError ())
load_dynamic_too_maybe logger name_cache unit_state dflags wanted_mod iface loc
  | not (moduleIsDefinite (mi_module iface))
  = return (Succeeded ())
  | gopt Opt_BuildDynamicToo dflags
  = load_dynamic_too logger name_cache unit_state dflags wanted_mod iface loc
  | otherwise
  = return (Succeeded ())

load_dynamic_too
  :: Logger
  -> NameCache
  -> UnitState
  -> DynFlags
  -> Module
  -> ModIface
  -> ModLocation
  -> IO (MaybeErr MissingInterfaceError ())
load_dynamic_too logger name_cache unit_state dflags wanted_mod iface loc = do
  res <- read_file logger name_cache unit_state dflags wanted_mod (ml_dyn_hi_file loc)
  case res of
    Succeeded (dynIface, _)
      | mi_mod_hash (mi_final_exts iface) == mi_mod_hash (mi_final_exts dynIface)
        -> return (Succeeded ())
      | otherwise
        -> return $ Failed $ DynamicHashMismatchError wanted_mod loc
    Failed err
      -> return $ Failed $ FailedToLoadDynamicInterface wanted_mod err

read_file
  :: Logger
  -> NameCache
  -> UnitState
  -> DynFlags
  -> Module
  -> FilePath
  -> IO (MaybeErr ReadInterfaceError (ModIface, FilePath))
read_file logger name_cache unit_state dflags wanted_mod file_path = do
  trace_if logger (text "readIface" <+> text file_path)
  let wanted_mod' = case getModuleInstantiation wanted_mod of
                      (_, Nothing) -> wanted_mod
                      (_, Just indef_mod) -> instModuleToModule unit_state
                                             (uninstantiateInstantiatedModule indef_mod)
  read_result <- readIface dflags name_cache wanted_mod' file_path
  case read_result of
    Failed err -> return $ Failed err
    Succeeded iface -> return $ Succeeded (iface, file_path)

readIface
  :: DynFlags -> NameCache -> Module -> FilePath -> IO (MaybeErr ReadInterfaceError ModIface)
readIface dflags name_cache wanted_mod file_path = do
  let profile = targetProfile dflags
  res <- tryMost $ readBinIface profile name_cache CheckHiWay QuietBinIFace file_path
  case res of
    Right iface
      | wanted_mod == actual_mod -> return (Succeeded iface)
      | otherwise -> return (Failed err)
      where
        actual_mod = mi_module iface
        err = HiModuleNameMismatchWarn file_path wanted_mod actual_mod
    Left exn -> return (Failed (ExceptionOccurred file_path exn))

{- *********************************************************************
*                                                                      *
        Wired-in interface for GHC.Prim
*                                                                      *
********************************************************************* -}

cslPrimIface :: ModIface
cslPrimIface = empty_iface
  { mi_exports = cslPrimExports
  , mi_decls = []
  , mi_fixities = fixities
  , mi_final_exts = (mi_final_exts empty_iface) { mi_fix_fn = mkIfaceFixCache fixities }
  }
  where
    empty_iface = emptyFullModIface cSLASH_PRIM
    fixities = trace "cslPrimIface/fixities" []

{- *********************************************************************
*                                                                      *
                Printing interfaces
*                                                                      *
********************************************************************* -}

showIface :: Logger -> DynFlags -> UnitState -> NameCache -> FilePath -> IO ()
showIface logger dflags unit_state name_cache filename = do
  let profile = targetProfile dflags
      printer = logMsg logger MCOutput noSrcSpan . withPprStyle defaultDumpStyle

  iface <- readBinIface profile name_cache IgnoreHiWay (TraceBinIFace printer) filename

  let qualifyImportedNames mod _
        | mod == mi_module iface = NameUnqual
        | otherwise = NameNotInScope1
      name_ppr_ctx = QueryQualify qualifyImportedNames neverQualifyModules
                                  neverQualifyPackages alwaysPrintPromTick

  logMsg logger MCDump noSrcSpan
    $ withPprStyle (mkDumpStyle name_ppr_ctx)
    $ pprModIface unit_state iface

pprModIface :: UnitState -> ModIface -> SDoc
pprModIface unit_state iface@ModIface{ mi_final_exts = exts }
 = vcat [ text "interface"
                <+> ppr (mi_module iface) <+> pp_cs_src (mi_cs_src iface)
                <+> (if mi_pc iface then text "[pc]" else Outputable.empty)
                <+> integer hiVersion
        , nest 2 (text "interface hash:" <+> ppr (mi_iface_hash exts))
        , nest 2 (text "ABI hash:" <+> ppr (mi_mod_hash exts))
        , nest 2 (text "export-list hash:" <+> ppr (mi_exp_hash exts))
        , nest 2 (text "flag hash:" <+> ppr (mi_flag_hash exts))
        , nest 2 (text "opt_hash:" <+> ppr (mi_opt_hash exts))
        , nest 2 (text "pc_hash:" <+> ppr (mi_pc_hash exts))
        , nest 2 (text "src_hash:" <+> ppr (mi_src_hash iface))
        , nest 2 (text "where")
        , text "exports:"
        , nest 2 (vcat (map pprExport (mi_exports iface)))
        , pprDeps unit_state (mi_deps iface)
        , vcat (map pprUsage (mi_usages iface))
        , vcat (map pprIfaceAnnotation (mi_anns iface))
        , pprFixities (mi_fixities iface)
        , vcat [ppr ver $$ nest 2 (ppr decl) | (ver,decl) <- mi_decls iface]
        , case mi_extra_decls iface of
            Nothing -> empty
            Just eds -> text "extra decls:"
                          $$ nest 2 (vcat ([ppr bs | bs <- eds]))
        , vcat (map ppr (mi_complete_matches iface))
        ]
  where
    pp_cs_src CsSrcFile  = Outputable.empty

pprExport :: IfaceExport -> SDoc
pprExport (Avail n) = ppr n
pprExport (AvailTC _ []) = Outputable.empty
pprExport avail@(AvailTC n _) =
  ppr n <> mark <> pp_export (availSubordinateNames avail)
  where
    mark | availExportsDecl avail = Outputable.empty
         | otherwise = vbar

    pp_export [] = Outputable.empty
    pp_export names = braces (hsep (map ppr names))

pprUsage :: Usage -> SDoc
pprUsage usage@UsagePackageModule{} = pprUsageImport usage usg_mod
pprUsage usage@UsageHomeModule{}
  = pprUsageImport usage (\u -> mkModule (usg_unit_id u) (usg_mod_name u)) $$
    nest 2 ( maybe Outputable.empty (\v -> text "exports: " <> ppr v) (usg_exports usage) $$
             vcat [ ppr n <+> ppr v | (n, v) <- usg_entities usage ]
           )

pprUsageImport :: Outputable a => Usage -> (Usage -> a) -> SDoc
pprUsageImport usage usg_mod'
  = hsep [ text "import"
         , ppr (usg_mod' usage)
         , ppr (usg_mod_hash usage)
         ]

pprFixities :: [(OccName, Fixity)] -> SDoc
pprFixities [] = Outputable.empty
pprFixities fixes = text "fixities" <+> pprWithCommas pprFix fixes
  where
    pprFix (occ, fix) = ppr fix <+> ppr occ

pprIfaceAnnotation :: IfaceAnnotation -> SDoc
pprIfaceAnnotation = undefined

data WhereFrom
  = ImportByUser
  | ImportBySystem

instance Outputable WhereFrom where
  ppr ImportByUser = empty
  ppr ImportBySystem = text "{- SYSTEM -}"
