{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}

module CSlash.Types.PkgQual where

import CSlash.Types.SourceText
import CSlash.Unit.Types
import CSlash.Utils.Outputable

import Data.Data

data RawPkgQual
  = NoRawPkgQual
  | RawPkgQual StringLiteral
  deriving (Data)

data PkgQual
  = NoPkgQual
  | ThisPkg UnitId
  | OtherPkg UnitId
  deriving (Data, Ord, Eq)

instance Outputable RawPkgQual where
  ppr = \case
    NoRawPkgQual -> empty
    RawPkgQual (StringLiteral st p _)
      -> pprWithSourceText st (doubleQuotes (ftext p))

instance Outputable PkgQual where
  ppr = \case
    NoPkgQual -> empty
    ThisPkg u -> doubleQuotes (ppr u)
    OtherPkg u -> doubleQuotes (ppr u)
