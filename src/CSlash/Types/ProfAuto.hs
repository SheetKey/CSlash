module CSlash.Types.ProfAuto where

data ProfAuto
  = NoProfAuto
  | ProfAutoAll
  | ProfAutoTop
  | ProfAutoExports
  | ProfAutoCalls
  deriving (Eq, Enum)
