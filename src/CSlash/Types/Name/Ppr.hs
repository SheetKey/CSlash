module CSlash.Types.Name.Ppr where

import CSlash.Data.FastString

import CSlash.Unit
import CSlash.Unit.Env

import CSlash.Types.Name
import CSlash.Types.Name.Reader


import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc
import CSlash.Builtin.Types.Prim ( fUNTyConName )
import CSlash.Builtin.Types
import Data.Maybe (isJust)

mkNamePprCtx :: Outputable info => UnitEnv -> GlobalRdrEnvX info -> NamePprCtx
mkNamePprCtx unit_env env
  = QueryQualify (mkQualName env)
                 (mkQualModule unit_state home_unit)
                 (mkQualPackage unit_state)
                 (const False)
  where
    unit_state = ue_units unit_env
    home_unit = ue_homeUnit unit_env

mkQualName :: Outputable info => GlobalRdrEnvX info -> QueryQualifyName
mkQualName env = qual_name
  where
    qual_name mod occ
      | [gre] <- unqual_gres
      , right_name gre
      = NameUnqual
      | [] <- unqual_gres
      , pretendNameIsInScopeForPpr
      , not (isDerivedOccName occ)
      = NameUnqual
      | [gre] <- qual_gres
      = NameQual (greQualModName gre)
      | [] <- qual_gres
      = if null $ lookupGRE env $ LookupRdrName (mkRdrQual (moduleName mod) occ) SameNameSpace
        then NameNotInScope1
        else NameNotInScope2
      | otherwise
      = NameNotInScope1
      where
        is_name :: Name -> Bool
        is_name name = assertPpr (isExternalName name) (ppr name) $
                       nameModule name == mod && nameOccName name == occ

        pretendNameIsInScopeForPpr :: Bool
        pretendNameIsInScopeForPpr =
          any is_name
            [ fUNTyConName ]
          || isJust (isTupleTyOcc_maybe mod occ)
          || isJust (isSumTyOcc_maybe mod occ)

        right_name gre = greDefinitionModule gre == Just mod

        unqual_gres = lookupGRE env $ LookupRdrName (mkRdrUnqual occ) SameNameSpace
        qual_gres = filter right_name $ lookupGRE env $ LookupOccName occ SameNameSpace

mkQualModule :: UnitState -> Maybe HomeUnit -> QueryQualifyModule
mkQualModule unit_state mhome_unit mod
  | Just home_unit <- mhome_unit
  , isHomeModule home_unit mod
  = False
  | [(_, pkgconfig)] <- lookup
  , mkUnit pkgconfig == moduleUnit mod
  = False
  | otherwise
  = True
  where lookup = lookupModuleInAllUnits unit_state $ moduleName mod

mkQualPackage :: UnitState -> QueryQualifyPackage
mkQualPackage pkgs uid
  | uid == mainUnit
  = False
  | Just pkgid <- mb_pkgid
  , searchPackageId pkgs pkgid `lengthIs` 1
  = False
  | otherwise
  = True
  where mb_pkgid = fmap unitPackageId (lookupUnit pkgs uid)
