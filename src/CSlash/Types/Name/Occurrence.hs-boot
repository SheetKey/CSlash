module CSlash.Types.Name.Occurrence where

import CSlash.Data.FastString ( FastString )

data OccName

class HasOccName name where
  occName :: name -> OccName

occNameFS :: OccName -> FastString

mkVarOccFS :: FastString -> OccName