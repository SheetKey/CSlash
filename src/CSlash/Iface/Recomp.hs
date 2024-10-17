{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE DeriveFunctor #-}

module CSlash.Iface.Recomp where

import Prelude hiding ((<>))

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
import CSlash.Iface.Recomp.Flags
import CSlash.Iface.Env

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
import CSlash.Unit.State hiding (comparing)
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
import CSlash.Iface.Errors.Ppr

data RecompileRequired
  = UpToDate
  | NeedsRecompile !CompileReason
  deriving Eq

needsRecompileBecause :: RecompReason -> RecompileRequired
needsRecompileBecause = NeedsRecompile . RecompBecause

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
  | OptimFlagsChanged
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
    OptimFlagsChanged -> text "Optimisation flags changed"
    PcFlagsChanged -> text "PC flags changed"
    MissingObjectFile -> text "Missing object file"
    MissingDynObjectFile -> text "Missing dynamic object file"
    MissingDynHiFile -> text "Missing dynamic interface file"
    MismatchedDynHiFile -> text "Mismatched dynamic interface file"
    ObjectsChange -> text "Objects changed"
    LibraryChanged -> text "Library changed"

recompileRequired :: RecompileRequired -> Bool
recompileRequired UpToDate = False
recompileRequired _ = True

recompThen :: Monad m => m RecompileRequired -> m RecompileRequired -> m RecompileRequired
recompThen ma mb = ma >>= \case
  UpToDate -> mb
  rr@(NeedsRecompile _) -> pure rr  

checkList :: Monad m => [m RecompileRequired] -> m RecompileRequired
checkList [] = return UpToDate
checkList (check:checks) = check `recompThen` checkList checks

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
check_old_iface cs_env mod_summary maybe_iface =
  let dflags = cs_dflags cs_env
      logger = cs_logger cs_env
      getIface = case maybe_iface of
        Just _ -> do
          trace_if logger (text "We already have the old interface for" <+>
                           ppr (ms_mod mod_summary))
          return maybe_iface
        Nothing -> loadIface dflags (msHiFilePath mod_summary)

      loadIface read_dflags iface_path = do
        let ncu = cs_NC cs_env
        read_result <- readIface read_dflags ncu (ms_mod mod_summary) iface_path
        case read_result of
          Failed err -> do
            let msg = readInterfaceErrorDiagnostic err
            trace_if logger $ vcat [ text "FYI: cannot read old interface file:"
                                   , nest 4 msg ]
            trace_hi_diffs logger $ vcat [ text "Old interface file was invalid:"
                                         , nest 4 msg ]
            return Nothing
          Succeeded iface -> do
            trace_if logger $ text "Read the interface file" <+> text iface_path
            return $ Just iface

      check_dyn_hi :: ModIface -> IfG (MaybeValidated ModIface) -> IfG (MaybeValidated ModIface)
      check_dyn_hi normal_iface recomp_check
        | gopt Opt_BuildDynamicToo dflags = do
            res <- recomp_check
            case res of
              UpToDateItem _ -> do
                maybe_dyn_iface <- liftIO
                  $ loadIface (setDynamicNow dflags) (msDynHiFilePath mod_summary)
                case maybe_dyn_iface of
                  Nothing -> return $ outOfDateItemBecause MissingDynHiFile Nothing
                  Just dyn_iface | mi_iface_hash (mi_final_exts dyn_iface)
                                   /= mi_iface_hash (mi_final_exts normal_iface)
                                   -> return $ outOfDateItemBecause MismatchedDynHiFile Nothing
                  Just _ -> return res
              _ -> return res
      check_dyn_hi _ recomp_check = recomp_check

      src_changed = gopt Opt_ForceRecomp dflags 

  in do
    when src_changed $
      liftIO $ trace_hi_diffs logger (nest 4 $ text "Recompilation check turned off")

    if | src_changed && not (backendWritesFiles $ backend dflags)
         -> return $ OutOfDateItem MustCompile maybe_iface
       | src_changed
         -> do maybe_iface' <- liftIO getIface
               return $ OutOfDateItem MustCompile maybe_iface'
       | otherwise
         -> do maybe_iface' <- liftIO getIface
               case maybe_iface' of
                 Nothing -> return $ OutOfDateItem MustCompile Nothing
                 Just iface -> check_dyn_hi iface $ checkVersions cs_env mod_summary iface

checkVersions :: CsEnv -> ModSummary -> ModIface -> IfG (MaybeValidated ModIface)
checkVersions cs_env mod_summary iface = do
  liftIO $ trace_hi_diffs logger
    (text "Considering whether compilation is required for"
     <+> ppr (mi_module iface) <> colon)

  cs_env <- getTopEnv
  if | mi_src_hash iface /= ms_cs_hash mod_summary
       -> return $ outOfDateItemBecause SourceFileChanged Nothing
     | not (isHomeModule home_unit (mi_module iface))
       -> return $ outOfDateItemBecause ThisUnitIdChanged Nothing
     | otherwise
       -> do recomp <- liftIO $ checkFlagHash cs_env iface
                                `recompThen` checkOptimHash cs_env iface
                                `recompThen` checkPcHash cs_env iface
                                `recompThen` pure (checkHie dflags mod_summary)
             case recomp of
               NeedsRecompile reason -> return $ OutOfDateItem reason Nothing
               _ -> do recomp <- checkDependencies cs_env mod_summary iface
                       case recomp of
                         NeedsRecompile reason -> return $ OutOfDateItem reason (Just iface)
                         _ -> do recomp <- checkList [ checkModUsage (cs_FC cs_env) u
                                                     | u <- mi_usages iface ]
                                 case recomp of
                                   NeedsRecompile reason ->
                                     return $ OutOfDateItem reason (Just iface)
                                   _ -> return $ UpToDateItem iface
  where
    logger = cs_logger cs_env
    dflags = cs_dflags cs_env
    home_unit = cs_home_unit cs_env

checkHie :: DynFlags -> ModSummary -> RecompileRequired
checkHie dflags mod_summary =
  let hie_date_opt = ms_hie_date mod_summary
      hi_date = ms_iface_date mod_summary
  in if not (gopt Opt_WriteHie dflags)
     then UpToDate
     else case (hie_date_opt, hi_date) of
            (Nothing, _) -> needsRecompileBecause HieMissing
            (Just hie_date, Just hi_date)
              | hie_date < hi_date
                -> needsRecompileBecause HieOutdated
            _ -> UpToDate
    
checkFlagHash :: CsEnv -> ModIface -> IO RecompileRequired
checkFlagHash cs_env iface = do
  let logger = cs_logger cs_env
      old_hash = mi_flag_hash (mi_final_exts iface)
  new_hash <- fingerprintDynFlags cs_env (mi_module iface) putNameLiterally
  if old_hash == new_hash
    then up_to_date logger (text "Module flags unchanged")
    else out_of_date_hash logger FlagsChanged
         (text "  Module flags have changed")
         old_hash new_hash

checkOptimHash :: CsEnv -> ModIface -> IO RecompileRequired
checkOptimHash cs_env iface = do
  let logger = cs_logger cs_env
      old_hash = mi_opt_hash (mi_final_exts iface)
  new_hash <- fingerprintOptFlags (cs_dflags cs_env) putNameLiterally
  if | old_hash == new_hash
       -> up_to_date logger (text "Optimization flags unchanged")
     | gopt Opt_IgnoreOptimChanges (cs_dflags cs_env)
       -> up_to_date logger (text "Optimization flags changed; ignoring")
     | otherwise
       -> out_of_date_hash logger OptimFlagsChanged
          (text "  Optimization flags have changes")
          old_hash new_hash

checkPcHash :: CsEnv -> ModIface -> IO RecompileRequired
checkPcHash cs_env iface = do
  let logger = cs_logger cs_env
      old_hash = mi_pc_hash (mi_final_exts iface)
  new_hash <- fingerprintPcFlags (cs_dflags cs_env) putNameLiterally
  if | old_hash == new_hash
       -> up_to_date logger (text "PC flags unchanged")
     | gopt Opt_IgnorePcChanges (cs_dflags cs_env)
       -> up_to_date logger (text "PC flags changed; ignoring")
     | otherwise
       -> out_of_date_hash logger PcFlagsChanged
          (text "  PC flags have changed")
          old_hash new_hash

checkDependencies :: CsEnv -> ModSummary -> ModIface -> IfG RecompileRequired
checkDependencies cs_env summary iface = do
  res_normal <- classify_import (findImportedModule cs_env) (ms_textual_imps summary)
  case sequence (res_normal ++ [Right (fake_csl_prim_import) | ms_csl_prim_import summary]) of
    Left recomp -> return $ NeedsRecompile recomp
    Right es -> 
      let (hs, ps) = partitionEithers es
      in liftIO $ check_mods (sort hs) prev_dep_mods
         `recompThen`
         let allPkgDeps = sortBy (comparing snd) $ nubOrdOn snd ps
         in check_packages allPkgDeps prev_dep_pkgs
  where
    classify_import
      :: (ModuleName -> t -> IO FindResult)
      -> [(t, GenLocated l ModuleName)]
      -> IfG [Either CompileReason (Either (UnitId, ModuleName) (FastString, UnitId))]
    classify_import find_import imports =
      liftIO $ traverse (\(mb_pkg, L _ mod) ->
                           let reason = ModuleChanged mod
                           in classify reason <$> find_import mod mb_pkg
                        ) imports

    dflags = cs_dflags cs_env
    fopts = initFinderOpts dflags
    logger = cs_logger cs_env
    fc = cs_FC cs_env
    mhome_unit = cs_home_unit_maybe cs_env
    all_home_units = cs_all_home_unit_ids cs_env
    units = cs_units cs_env
    prev_dep_mods = Set.toAscList $ dep_direct_mods (mi_deps iface)
    prev_dep_pkgs = Set.toAscList (dep_direct_pkgs (mi_deps iface))

    fake_csl_prim_import = case mhome_unit of
                             Just home_unit
                               | homeUnitId home_unit == primUnitId
                                 -> Left (primUnitId, mkModuleName "CSL.Prim")
                             _ -> Right (fsLit "CSL.Prim", primUnitId)

    classify _ (Found _ mod)
      | (toUnitId $ moduleUnit mod) `elem` all_home_units
      = Right (Left ((toUnitId $ moduleUnit mod), moduleName mod))
      | otherwise = Right (Right (moduleNameFS (moduleName mod), toUnitId $ moduleUnit mod))
    classify reason _ = Left (RecompBecause reason)

    check_mods :: [(UnitId, ModuleName)] -> [(UnitId, ModuleName)] -> IO RecompileRequired
    check_mods [] [] = return UpToDate
    check_mods [] (old:_) = do
      trace_hi_diffs logger $ text "module no longer"
                              <+> quotes (ppr old)
                              <+> text "in dependencies"
      return $ needsRecompileBecause $ ModuleRemoved old
    check_mods (new:news) (old:olds)
      | new == old
      = check_mods (dropWhile (== new) news) olds
    check_mods (new:news) olds = do
      trace_hi_diffs logger $ text "imported module " <> quotes (ppr new) <>
                              text "not among previous dependencies"
      return $ needsRecompileBecause $ ModuleAdded new

    check_packages :: [(FastString, UnitId)] -> [UnitId] -> IO RecompileRequired
    check_packages [] [] = return UpToDate
    check_packages [] (old:_) = do
      trace_hi_diffs logger $ text "packages " <> quotes (ppr old) 
                              <> text "no longer in dependencies"
      return $ needsRecompileBecause $ UnitDepRemoved old
    check_packages ((new_name, new_unit):news) (old:olds)
      | new_unit == old
      = check_packages (dropWhile ((== new_unit) . snd) news) olds
    check_packages ((new_name, new_unit):news) olds = do
      trace_hi_diffs logger $ text "imported package" <+> ftext new_name <+> ppr new_unit
                              <+> text "not among previous dependencies"
      return $ needsRecompileBecause $ ModulePackageChanged new_name

needInterface
  :: Module -> (ModIface -> IO RecompileRequired) -> IfG RecompileRequired
needInterface mod continue = do
  mb_recomp <- tryGetModIface "need version info for" mod
  case mb_recomp of
    Nothing -> return $ NeedsRecompile MustCompile
    Just iface -> liftIO $ continue iface

tryGetModIface :: String -> Module -> IfG (Maybe ModIface)
tryGetModIface doc_msg mod = do
  logger <- getLogger
  let doc_str = sep [text doc_msg, ppr mod]
  liftIO $ trace_hi_diffs logger (text "Checking interface for module"
                                  <+> ppr mod <+> ppr (moduleUnit mod))

  mb_iface <- loadInterface doc_str mod ImportBySystem

  case mb_iface of
    Failed _ -> do
      liftIO $ trace_hi_diffs logger (sep [text "Couldn't load interface for module", ppr mod])
      return Nothing
    Succeeded iface -> pure $ Just iface

checkModUsage :: FinderCache -> Usage -> IfG RecompileRequired
checkModUsage _ UsagePackageModule { usg_mod = mod, usg_mod_hash = old_mod_hash } = do
  logger <- getLogger
  needInterface mod $ \iface -> 
    let reason = ModuleChanged (moduleName mod)
    in checkModuleFingerprint logger reason old_mod_hash (mi_mod_hash (mi_final_exts iface))
checkModUsage _ UsageHomeModule { usg_mod_name = mod_name
                                , usg_unit_id = uid
                                , usg_mod_hash = old_mod_hash
                                , usg_exports = maybe_old_export_hash
                                , usg_entities = old_decl_hash } = do
  let mod = mkModule (RealUnit (Definite uid)) mod_name
  logger <- getLogger
  needInterface mod $ \iface ->
    let new_mod_hash = mi_mod_hash (mi_final_exts iface)
        new_decl_hash = mi_hash_fn (mi_final_exts iface)
        new_export_hash = mi_exp_hash (mi_final_exts iface)

        reason = ModuleChanged (moduleName mod)
    in liftIO $ do
      recompile <- checkModuleFingerprint logger reason old_mod_hash new_mod_hash
      if not (recompileRequired recompile)
        then return UpToDate
        else checkList [ checkMaybeHash logger reason maybe_old_export_hash new_export_hash
                         (text "  Export list changed")
                       , checkList [ checkEntityUsage logger reason new_decl_hash u
                                   | u <- old_decl_hash ]
                       , up_to_date logger (text "  Great! The bits I use are up to date")
                       ]

checkModuleFingerprint
  :: Logger
  -> RecompReason
  -> Fingerprint
  -> Fingerprint
  -> IO RecompileRequired
checkModuleFingerprint logger reason old_mod_hash new_mod_hash
  | new_mod_hash == old_mod_hash
  = up_to_date logger (text "Module fingerprint unchanged")
  | otherwise
  = out_of_date_hash logger reason (text "  Module fingerprint has changed")
    old_mod_hash new_mod_hash

checkMaybeHash
  :: Logger
  -> RecompReason
  -> Maybe Fingerprint
  -> Fingerprint
  -> SDoc
  -> IO RecompileRequired
checkMaybeHash logger reason maybe_old_hash new_hash doc
  | Just hash <- maybe_old_hash
  , hash /= new_hash
  = out_of_date_hash logger reason doc hash new_hash
  | otherwise
  = return UpToDate

checkEntityUsage
  :: Logger
  -> RecompReason
  -> (OccName -> Maybe (OccName, Fingerprint))
  -> (OccName, Fingerprint)
  -> IO RecompileRequired
checkEntityUsage logger reason new_hash (name, old_hash) = do
  case new_hash name of
    Nothing -> out_of_date logger reason (sep [text "No longer exported:", ppr name])
    Just (_, new_hash)
      | new_hash == old_hash
        -> do trace_hi_diffs logger (text "  Up to date" <+> ppr name <+> parens (ppr new_hash))
              return UpToDate
      | otherwise
        -> out_of_date_hash logger reason (text "  Out of date:" <+> ppr name) old_hash new_hash

up_to_date :: Logger -> SDoc -> IO RecompileRequired
up_to_date logger msg = trace_hi_diffs logger msg >> return UpToDate
        
out_of_date :: Logger -> RecompReason -> SDoc -> IO RecompileRequired
out_of_date logger reason msg = trace_hi_diffs logger msg >> return (needsRecompileBecause reason)

out_of_date_hash
  :: Logger -> RecompReason -> SDoc -> Fingerprint -> Fingerprint -> IO RecompileRequired
out_of_date_hash logger reason msg old_hash new_hash =
  out_of_date logger reason (hsep [msg, ppr old_hash, text "->", ppr new_hash])
