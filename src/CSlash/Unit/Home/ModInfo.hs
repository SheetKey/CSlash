module CSlash.Unit.Home.ModInfo where

import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.ModDetails
import CSlash.Unit.Module

import CSlash.Linker.Types ( Linkable(..){-, isObjectLinkable-} )

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

data HomeModLinkable = HomeModLinkable
  { homeMod_object :: !(Maybe Linkable) }

type HomePackageTable = DModuleNameEnv HomeModInfo

emptyHomePackageTable :: HomePackageTabel
emptyHomePackageTable = emptyUDFM

pprHPT :: HomePackageTable -> SDoc
pprHPT hpt = pprUDFM hpt $ \hms ->
  vcat [ ppr (mi_module (hm_iface hm))
       | hm <- hms
       ]
