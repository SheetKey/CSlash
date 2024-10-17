module CSlash.Unit.Home.ModInfo where

import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.ModDetails
import CSlash.Unit.Module

import CSlash.Linker.Types ( Linkable(..), isObjectLinkable )

import CSlash.Types.Unique
import CSlash.Types.Unique.DFM

import CSlash.Utils.Outputable
import Data.List (sortOn)
import Data.Ord
import CSlash.Utils.Panic

data HomeModInfo = HomeModInfo
  { hm_iface :: !ModIface
  , hm_details :: ModDetails
  , hm_linkable :: !HomeModLinkable
  }

emptyHomeModInfoLinkable :: HomeModLinkable
emptyHomeModInfoLinkable = HomeModLinkable Nothing

data HomeModLinkable = HomeModLinkable
  { homeMod_object :: !(Maybe Linkable) }

instance Outputable HomeModLinkable where
  ppr (HomeModLinkable l1) = ppr l1

justObjects :: Linkable -> HomeModLinkable
justObjects lm = assertPpr (isObjectLinkable lm) (ppr lm) $
  emptyHomeModInfoLinkable { homeMod_object = Just lm }

type HomePackageTable = DModuleNameEnv HomeModInfo

emptyHomePackageTable :: HomePackageTable
emptyHomePackageTable = emptyUDFM

lookupHpt :: HomePackageTable -> ModuleName -> Maybe HomeModInfo
lookupHpt = lookupUDFM

anyHpt :: (HomeModInfo -> Bool) -> HomePackageTable -> Bool
anyHpt = anyUDFM          

addToHpt :: HomePackageTable -> ModuleName -> HomeModInfo -> HomePackageTable
addToHpt = addToUDFM

addHomeModInfoToHpt :: HomeModInfo -> HomePackageTable -> HomePackageTable
addHomeModInfoToHpt hmi hpt = addToHpt hpt (moduleName (mi_module (hm_iface hmi))) hmi

addListToHpt :: HomePackageTable -> [(ModuleName, HomeModInfo)] -> HomePackageTable
addListToHpt = addListToUDFM

lookupHptByModule :: HomePackageTable -> Module -> Maybe HomeModInfo
lookupHptByModule hpt mod = case lookupHpt hpt (moduleName mod) of
  Just hm | mi_module (hm_iface hm) == mod -> Just hm
  _ -> Nothing

pprHPT :: HomePackageTable -> SDoc
pprHPT hpt = pprUDFM hpt $ \hms ->
  vcat [ ppr (mi_module (hm_iface hm))
       | hm <- hms
       ]
