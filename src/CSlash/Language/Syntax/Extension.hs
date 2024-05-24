module CSlash.Language.Syntax.Extension where

data CsPass (c :: Pass) where
  Ps :: CsPass 'Parsed
  Rn :: CsPass 'Renamed
  Tc :: CsPass 'Typechecked

data Pass = Parsed | Renamed | Typechecked
         deriving (Data)

type Ps = Pass 'Parsed
type Rn = Pass 'Renamed
type Tc = Pass 'Typechecked

type family XRec p a = r | r -> a

class UnXRec p where
  unXRec :: XRec p a -> a

class MapXRec p where
  mapXRec :: (Anno a ~ Anno b) => (a -> b) -> XRec p a -> XRec p b

class WrapXRec p a where
  wrapXRec :: a -> XRec p a
