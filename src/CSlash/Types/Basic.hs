module CSlash.Types.Basic
  ( module X
  , pprAlternative
  ) where

import GHC.Types.Basic as X hiding
  (pprAlternative)

import CSlash.Utils.Outputable

pprAlternative :: (a -> SDoc) -> a -> ConTag -> Arity -> SDoc
pprAlternative pp x alt arity
  = fsep (replicate (alt - 1) vbar ++ [pp x] ++ replicate (arity - alt) vbar)

instance Outputable (TyConFlavour tc) where
  ppr = text . go
    where
      go (ClassFlavour) = "class"
      go (TupleFlavour _) = "tuple"
      go SumFlavour = "sum"
      go TypeSynonymFlavour = "type synonym"
      go _ = error "This 'TyConFlavour' should not be used yet"
