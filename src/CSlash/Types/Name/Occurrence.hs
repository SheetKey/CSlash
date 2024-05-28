module CSlash.Types.Name.Occurrence where

import CSlash.Data.FastString

data NameSpace
  = VarName
  | TvName
  | KvName

data OccName = OccName
  { occNameSpace :: !NameSpace
  , occNameFS :: !FastString
  }
