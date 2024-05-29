module CSlash.Cs.Extension where

data CsPass (c :: Pass) where
  Ps :: CsPass 'Parsed
  Rn :: CsPass 'Renamed
  Tc :: CsPass 'Typechecked

data Pass = Parsed | Renamed | Typechecked
         deriving (Data)

type Ps = CsPass 'Parsed
type Rn = CsPass 'Renamed
type Tc = CsPass 'Typechecked

