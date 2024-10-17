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
