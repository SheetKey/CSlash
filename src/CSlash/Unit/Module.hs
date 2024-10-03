{-# LANGUAGE RecordWildCards #-}

module CSlash.Unit.Module
  ( module CSlash.Unit.Types
  , module CSlash.Language.Syntax.Module.Name
  , module CSlash.Unit.Module.Location
  , module CSlash.Unit.Module.Env

  , getModuleInstantiation
  , getUnitInstantiations

  , mkHoleModule
  , isHoleModule
  , stableModuleCmp
  , moduleStableString
  , installedModuleEq
  ) where

import CSlash.Unit.Types
import CSlash.Language.Syntax.Module.Name
import CSlash.Unit.Module.Location
import CSlash.Unit.Module.Env

moduleStableString :: Module -> String
moduleStableString Module{..} =
  "$" ++ unitString moduleUnit ++ "$" ++ moduleNameString moduleName

stableModuleCmp :: Module -> Module -> Ordering
stableModuleCmp (Module p1 n1) (Module p2 n2) =
  stableUnitCmp p1 p2 <> stableModuleNameCmp n1 n2

installedModuleEq :: InstalledModule -> Module -> Bool
installedModuleEq imod mod =
  fst (getModuleInstantiation mod) == imod

{- *********************************************************************
*                                                                      *
                        Hole substitutions
*                                                                      *
********************************************************************* -}

getModuleInstantiation :: Module -> (InstalledModule, Maybe InstantiatedModule)
getModuleInstantiation m =
  let (uid, mb_iuid) = getUnitInstantiations (moduleUnit m)
  in ( Module uid (moduleName m)
     , fmap (\iuid -> Module iuid (moduleName m)) mb_iuid)

getUnitInstantiations :: Unit -> (UnitId, Maybe InstantiatedUnit)
getUnitInstantiations (VirtUnit iuid) = (instUnitInstanceOf iuid, Just iuid)
getUnitInstantiations (RealUnit (Definite uid)) = (uid, Nothing)
getUnitInstantiations (HoleUnit {}) = error "Hole unit"

isHoleModule :: GenModule (GenUnit u) -> Bool
isHoleModule (Module HoleUnit _) = True
isHoleModule _ = False

mkHoleModule :: ModuleName -> GenModule (GenUnit u)
mkHoleModule = Module HoleUnit
