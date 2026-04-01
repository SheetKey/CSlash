module CSlash.CsToCore.Usage where

import CSlash.Cs.Pass

import CSlash.Driver.Env

import CSlash.Tc.Types

import CSlash.Iface.Load

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Fingerprint
import CSlash.Utils.Panic
import CSlash.Utils.Monad

import CSlash.Types.Name
import CSlash.Types.Name.Set ( NameSet, allUses )
import CSlash.Types.Unique.Set

import CSlash.Unit
import CSlash.Unit.Env
import CSlash.Unit.External
import CSlash.Unit.Module.Imported
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.Deps

import CSlash.Data.Maybe
import CSlash.Data.FastString

import Data.IORef
import Data.List (sortBy)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List.NonEmpty as NE

import CSlash.Linker.Types
import CSlash.Unit.Finder
import CSlash.Types.Unique.DFM

mkUsedNames :: TcGblEnv Zk -> NameSet
mkUsedNames TcGblEnv { tcg_dus = dus } = allUses dus

mkUsageInfo
  :: FinderCache
  -> UnitEnv
  -> Module
  -> ImportedMods
  -> NameSet
  -> [(Module, Fingerprint)]
  -> IfG [Usage]
mkUsageInfo fc unit_env this_mod dir_imp_mods used_names merged = do
  eps <- liftIO $ readIORef (euc_eps (ue_eps unit_env))
  let hu = unsafeGetHomeUnit unit_env
      hug = ue_home_unit_graph unit_env

      all_home_ids = ue_all_home_unit_ids unit_env
  mod_usages <- mk_mod_usage_info hu all_home_ids this_mod dir_imp_mods used_names
  let usages = mod_usages ++ [ UsageMergedRequirement
                               { usg_mod = mod, usg_mod_hash = hash }
                             | (mod, hash) <- merged ]
  usages `seqList` return usages

mk_mod_usage_info
  :: HomeUnit
  -> Set.Set UnitId
  -> Module
  -> ImportedMods
  -> NameSet
  -> IfG [Usage]
mk_mod_usage_info home_unit home_unit_ids this_mod direct_imports used_names
  = mapMaybeM mkUsageM usage_mods
  where
    used_mods = moduleEnvKeys ent_map
    dir_imp_mods = Map.keys direct_imports
    all_mods = used_mods ++ filter (`notElem` used_mods) dir_imp_mods
    usage_mods = sortBy stableModuleCmp all_mods

    ent_map :: ModuleEnv [OccName]
    ent_map = nonDetStrictFoldUniqSet add_mv emptyModuleEnv used_names
      where
        add_mv name mv_map
          | isWiredInName name = mv_map
          | otherwise
          = case nameModule_maybe name of
              Nothing -> assertPpr (isSystemName name) (ppr name) mv_map
              Just mod -> let mod' = if isHoleModule mod
                                     then mkHomeModule home_unit (moduleName mod)
                                     else mod
                          in extendModuleEnvWith (\_ xs -> occ:xs) mv_map mod' [occ]
                where occ = nameOccName name

    mkUsageM :: Module -> IfG (Maybe Usage)
    mkUsageM mod
      | mod == this_mod = return Nothing
      | otherwise
      = do iface <- loadSysInterface (text "mk_mod_usage") mod
           return $ mkUsage mod iface

    mkUsage :: Module -> ModIface -> Maybe Usage
    mkUsage mod iface
      | toUnitId (moduleUnit mod) `Set.notMember` home_unit_ids
      = Just $ UsagePackageModule { usg_mod = mod
                                  , usg_mod_hash = mod_hash }
      | (null used_occs
         && isNothing export_hash
         && not is_direct_import)
      = Nothing
      | otherwise
      = Just UsageHomeModule { usg_mod_name = moduleName mod
                             , usg_unit_id = toUnitId (moduleUnit mod)
                             , usg_mod_hash = mod_hash
                             , usg_exports = export_hash
                             , usg_entities = Map.toList ent_hashs }
      where
        hash_env = mi_hash_fn (mi_final_exts iface)
        mod_hash = mi_mod_hash (mi_final_exts iface)
        export_hash | depend_on_exports = Just (mi_exp_hash (mi_final_exts iface))
                    | otherwise = Nothing

        is_direct_import = case Map.lookup mod direct_imports of
                             Just _ -> True
                             Nothing -> False

        used_occs = lookupModuleEnv ent_map mod `orElse` []

        ent_hashs :: Map OccName Fingerprint
        ent_hashs = Map.fromList (map lookup_occ used_occs)

        lookup_occ occ = case hash_env occ of
                           Nothing -> pprPanic "mkUsage" (ppr mod <+> ppr occ <+> ppr used_names)
                           Just r -> r

        depend_on_exports = is_direct_import                                  
