module CSlash.Unit.Home
   ( GenHomeUnit (..)
   , HomeUnit
   , homeUnitId
   , homeUnitInstantiations
   , homeUnitInstanceOf
   , homeUnitInstanceOfMaybe
   , homeUnitAsUnit
   , homeUnitMap

   , isHomeUnitIndefinite
   , isHomeUnitDefinite
   , isHomeUnitInstantiating
   , isHomeUnit
   , isHomeUnitId
   , isHomeUnitInstanceOf
   , isHomeModule
   , isHomeInstalledModule
   , notHomeUnitId
   , notHomeModule
   , notHomeModuleMaybe
   , notHomeInstalledModule
   , notHomeInstalledModuleMaybe

   , mkHomeModule
   , mkHomeInstalledModule
   , homeModuleInstantiation
   , homeModuleNameInstantiation
   )
where

import CSlash.Unit.Types
import Data.Maybe

import CSlash.Language.Syntax.Module.Name

data GenHomeUnit u
   = DefiniteHomeUnit UnitId (Maybe (u, GenInstantiations u))
   | IndefiniteHomeUnit UnitId (GenInstantiations u)

type HomeUnit = GenHomeUnit UnitId

homeUnitId :: GenHomeUnit u -> UnitId
homeUnitId (DefiniteHomeUnit u _)   = u
homeUnitId (IndefiniteHomeUnit u _) = u

homeUnitInstantiations :: GenHomeUnit u -> GenInstantiations u
homeUnitInstantiations (DefiniteHomeUnit   _ Nothing)       = []
homeUnitInstantiations (DefiniteHomeUnit   _ (Just (_,is))) = is
homeUnitInstantiations (IndefiniteHomeUnit _ is)            = is

homeUnitInstanceOf :: HomeUnit -> UnitId
homeUnitInstanceOf h = fromMaybe (homeUnitId h) (homeUnitInstanceOfMaybe h)

homeUnitInstanceOfMaybe :: GenHomeUnit u -> Maybe u
homeUnitInstanceOfMaybe (DefiniteHomeUnit   _ (Just (u,_))) = Just u
homeUnitInstanceOfMaybe _                                   = Nothing

homeUnitAsUnit :: HomeUnit -> Unit
homeUnitAsUnit (DefiniteHomeUnit u _)    = RealUnit (Definite u)
homeUnitAsUnit (IndefiniteHomeUnit u is) = mkVirtUnit u is

homeUnitMap :: IsUnitId v => (u -> v) -> GenHomeUnit u -> GenHomeUnit v
homeUnitMap _ (DefiniteHomeUnit u Nothing)       = DefiniteHomeUnit u Nothing
homeUnitMap f (DefiniteHomeUnit u (Just (i,is))) = DefiniteHomeUnit u (Just (f i, mapInstantiations f is))
homeUnitMap f (IndefiniteHomeUnit u is)          = IndefiniteHomeUnit u (mapInstantiations f is)

isHomeUnitIndefinite :: GenHomeUnit u -> Bool
isHomeUnitIndefinite (DefiniteHomeUnit {})   = False
isHomeUnitIndefinite (IndefiniteHomeUnit {}) = True

isHomeUnitDefinite :: GenHomeUnit u -> Bool
isHomeUnitDefinite (DefiniteHomeUnit {})   = True
isHomeUnitDefinite (IndefiniteHomeUnit {}) = False

isHomeUnitInstantiating :: GenHomeUnit u -> Bool
isHomeUnitInstantiating u =
   isHomeUnitDefinite u && not (null (homeUnitInstantiations u))

isHomeUnit :: HomeUnit -> Unit -> Bool
isHomeUnit hu u = u == homeUnitAsUnit hu

isHomeUnitId :: GenHomeUnit u -> UnitId -> Bool
isHomeUnitId hu uid = uid == homeUnitId hu

notHomeUnitId :: Maybe (GenHomeUnit u) -> UnitId -> Bool
notHomeUnitId Nothing   _   = True
notHomeUnitId (Just hu) uid = not (isHomeUnitId hu uid)

isHomeUnitInstanceOf :: HomeUnit -> UnitId -> Bool
isHomeUnitInstanceOf hu u = homeUnitInstanceOf hu == u

isHomeModule :: HomeUnit -> Module -> Bool
isHomeModule hu m = isHomeUnit hu (moduleUnit m)

isHomeInstalledModule :: GenHomeUnit u -> InstalledModule -> Bool
isHomeInstalledModule hu m = isHomeUnitId hu (moduleUnit m)

notHomeInstalledModule :: GenHomeUnit u -> InstalledModule -> Bool
notHomeInstalledModule hu m = not (isHomeInstalledModule hu m)

notHomeInstalledModuleMaybe :: Maybe (GenHomeUnit u) -> InstalledModule -> Bool
notHomeInstalledModuleMaybe mh m = fromMaybe True $ fmap (`notHomeInstalledModule` m) mh

notHomeModule :: HomeUnit -> Module -> Bool
notHomeModule hu m = not (isHomeModule hu m)

notHomeModuleMaybe :: Maybe HomeUnit -> Module -> Bool
notHomeModuleMaybe mh m = fromMaybe True $ fmap (`notHomeModule` m) mh

mkHomeModule :: HomeUnit -> ModuleName -> Module
mkHomeModule hu = mkModule (homeUnitAsUnit hu)

mkHomeInstalledModule :: GenHomeUnit u -> ModuleName -> InstalledModule
mkHomeInstalledModule hu = mkModule (homeUnitId hu)

homeModuleNameInstantiation :: HomeUnit -> ModuleName -> Module
homeModuleNameInstantiation hu mod_name =
    case lookup mod_name (homeUnitInstantiations hu) of
        Nothing  -> mkHomeModule hu mod_name
        Just mod -> mod

homeModuleInstantiation :: Maybe HomeUnit -> Module -> Module
homeModuleInstantiation mhu mod
   | Just hu <- mhu
   , isHomeModule hu mod = homeModuleNameInstantiation hu (moduleName mod)
   | otherwise           = mod
