module CSlash.Unit.Ppr where

import CSlash.Data.FastString
import CSlash.Utils.Outputable
import Data.Version

data UnitPprInfo = UnitPprInfo
  { unitPprId :: FastString
  , unitPprPackageName :: String
  , unitPprPackageVersion :: Version
  }

instance Outputable UnitPprInfo where
  ppr pprinfo = getPprDebug $ \debug ->
    if debug
    then ftext (unitPprId pprinfo)
    else text $ mconcat
         [ unitPprPackageName pprinfo
         , case unitPprPackageVersion pprinfo of
             Version [] [] -> ""
             version -> "-" ++ showVersion version
         ]
