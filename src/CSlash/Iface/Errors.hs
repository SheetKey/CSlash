module CSlash.Iface.Errors where

import CSlash.Platform.Profile
import CSlash.Platform.Ways
import CSlash.Utils.Panic.Plain
import CSlash.Driver.DynFlags
import CSlash.Driver.Env
import CSlash.Data.Maybe
import CSlash.Unit
import CSlash.Unit.Env
import CSlash.Unit.Finder.Types
import CSlash.Utils.Outputable as Outputable
import CSlash.Iface.Errors.Types

cannotFindInterface
  :: UnitState
  -> Maybe HomeUnit
  -> Profile
  -> ModuleName
  -> InstalledFindResult
  -> MissingInterfaceError
cannotFindInterface us mhu p mn ifr = CantFindErr us FindingInterface $
  cantFindInstalledErr us mhu p mn ifr

cantFindInstalledErr
    :: UnitState
    -> Maybe HomeUnit
    -> Profile
    -> ModuleName
    -> InstalledFindResult
    -> CantFindInstalled
cantFindInstalledErr unit_state mhome_unit profile mod_name find_result
  = CantFindInstalled mod_name more_info
  where
    build_tag  = waysBuildTag (profileWays profile)

    more_info = case find_result of
      InstalledNoPackage pkg
        -> NoUnitIdMatching pkg (searchPackageId unit_state (PackageId (unitIdFS pkg)))
      InstalledNotFound files mb_pkg
        | Just pkg <- mb_pkg
        , notHomeUnitId mhome_unit pkg
          -> not_found_in_package pkg files
        | null files
          -> NotAModule
        | otherwise
          -> CouldntFindInFiles files
      _ -> panic "cantFindInstalledErr"

    not_found_in_package pkg files
      | build_tag /= ""
      = let build = if build_tag == "p"
                    then "profiling"
                    else "\"" ++ build_tag ++ "\""
        in MissingPackageWayFiles build pkg files
      | otherwise
      = MissingPackageFiles pkg files

cannotFindModule :: CsEnv -> ModuleName -> FindResult -> MissingInterfaceError
cannotFindModule cs_env = cannotFindModule' (cs_unit_env cs_env) (targetProfile (cs_dflags cs_env))

cannotFindModule' :: UnitEnv -> Profile -> ModuleName -> FindResult -> MissingInterfaceError
cannotFindModule' unit_env profile mod res =
  CantFindErr (ue_units unit_env) FindingModule $
  cantFindErr unit_env profile mod res
      
cantFindErr :: UnitEnv -> Profile -> ModuleName -> FindResult -> CantFindInstalled
cantFindErr _ _ mod_name (FoundMultiple mods)
  = CantFindInstalled mod_name (MultiplePackages mods)
cantFindErr unit_env profile mod_name find_result
  = CantFindInstalled mod_name more_info
  where
    mhome_unit = ue_homeUnit unit_env
    more_info = case find_result of
      NoPackage pkg -> NoUnitIdMatching (toUnitId pkg) []
      NotFound { fr_paths =files, fr_pkg = mb_pkg
               , fr_mods_hidden = mod_hiddens, fr_pkgs_hidden = pkg_hiddens
               , fr_unusables = unusables, fr_suggestions = suggest }
        | Just pkg <- mb_pkg
        , Nothing <- mhome_unit
          -> not_found_in_package (toUnitId pkg) files

        | Just pkg <- mb_pkg
        , Just home_unit <- mhome_unit
        , not (isHomeUnit home_unit pkg)
          -> not_found_in_package (toUnitId pkg) files

        | not (null suggest)
          -> ModuleSuggestion suggest files

        | null files && null mod_hiddens && null pkg_hiddens && null unusables
          -> NotAModule

        | otherwise
          -> GenericMissing
             (map (\uid -> (uid, lookupUnit (ue_units unit_env) uid)) pkg_hiddens)
             mod_hiddens unusables files

      _ -> panic "cantFindErr"

    build_tag = waysBuildTag (profileWays profile)

    not_found_in_package pkg files
      | build_tag /= ""
      = let build = if build_tag == "p" then "profiling" else "\"" ++ build_tag ++ "\""
        in MissingPackageWayFiles build pkg files
      | otherwise
      = MissingPackageFiles pkg files
