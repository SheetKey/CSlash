module CSlash.Unit.Module where

import CSlash.Unit.Types

isHoleModule :: GenModule (GenUnit u) -> Bool
isHoleModule (Moudle HoleUnit _) = True
isHoleModule _ = False
