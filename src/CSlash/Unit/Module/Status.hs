module CSlash.Unit.Module.Status where

import CSlash.Unit
import CSlash.Unit.Module.ModGuts
import CSlash.Unit.Module.ModIface

import CSlash.Utils.Fingerprint
import CSlash.Utils.Outputable
import CSlash.Unit.Home.ModInfo

data CsRecompStatus
  = CsUpToDate ModIface HomeModLinkable
  | CsRecompNeeded (Maybe Fingerprint)

data CsBackendAction
  = CsUpdate ModIface
  | CsRecomp
    { cs_guts :: CgGuts
    , cs_mod_location :: !ModLocation
    , cs_partial_iface :: !PartialModIface
    , cs_old_iface_hash :: !(Maybe Fingerprint)
    }

instance Outputable CsBackendAction where
  ppr (CsUpdate mi) = text "Update:" <+> (ppr (mi_module mi))
  ppr (CsRecomp _ ml _ _) = text "Recomp:" <+> ppr ml
