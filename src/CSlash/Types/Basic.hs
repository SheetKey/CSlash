{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Types.Basic
  ( ConTag

  , maybeParen

  , pprAlternative

  , TyConFlavor(..), tyConFlavorAssoc_maybe

  , module X
  ) where

import GHC.Types.Basic as X hiding
  ( TyConFlavour(..)
  , ConTag
  , pprAlternative
  , maybeParen
  )
  
import CSlash.Language.Syntax.Basic
import CSlash.Utils.Outputable

import Control.DeepSeq
import Data.Data

maybeParen :: PprPrec -> PprPrec -> SDoc -> SDoc
maybeParen ctxt_prec inner_prec pretty
  | ctxt_prec < inner_prec = pretty
  | otherwise = parens pretty

pprAlternative :: (a -> SDoc) -> a -> ConTag -> Arity -> SDoc
pprAlternative pp x alt arity
  = fsep (replicate (alt - 1) vbar ++ [pp x] ++ replicate (arity - alt) vbar)

data TyConFlavor tc
  = TupleFlavor
  | SumFlavor
  | DataTypeFlavor
  | AbstractTypeFlavor
  | TypeFunFlavor
  | BuiltInTypeFlavor
  deriving (Eq, Data, Functor)

instance Outputable (TyConFlavor tc) where
  ppr = text . go
    where
      go TupleFlavor = "tuple"
      go SumFlavor = "sum"
      go TypeFunFlavor = "type synonym"
      go DataTypeFlavor = "data type"
      go AbstractTypeFlavor = "abstract type"
      go BuiltInTypeFlavor = "built-in type"

instance NFData tc => NFData (TyConFlavor tc) where
  rnf TupleFlavor = ()
  rnf SumFlavor = ()
  rnf TypeFunFlavor = ()
  rnf DataTypeFlavor = ()
  rnf AbstractTypeFlavor = ()
  rnf BuiltInTypeFlavor = ()

tyConFlavorAssoc_maybe :: TyConFlavor tc -> Maybe tc
tyConFlavorAssoc_maybe _ = Nothing

instance Outputable TopLevelFlag where
  ppr TopLevel = text "<TopLevel>"
  ppr NotTopLevel = text "<NotTopLevel>"
