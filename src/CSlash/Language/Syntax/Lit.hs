{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Language.Syntax.Lit where

import CSlash.Language.Syntax.Extension

import CSlash.Types.SourceText
import CSlash.Data.FastString
import CSlash.Utils.Panic

import Data.Data hiding (Fixity)

data CsLit x
  = CsChar (XCsChar x) {- SourceText -} Char
  -- Probably don't use the following three:
  -- these should all be CsOverLit, at least during parsing.
  | CsString (XCsString x) {- SourceText -} FastString
  | CsInt (XCsInt x) IntegralLit
  | CsDouble (XCsDouble x) FractionalLit

data CsOverLit p = OverLit
  { ol_ext :: (XOverLit p)
  , ol_val :: OverLitVal
  }

data OverLitVal
  = CsIntegral !IntegralLit
  | CsFractional !FractionalLit
  | CsIsString !SourceText !FastString
  deriving Data

negateOverLitVal :: OverLitVal -> OverLitVal
negateOverLitVal (CsIntegral i) = CsIntegral (negateIntegralLit i)
negateOverLitVal (CsFractional f) = CsFractional (negateFractionalLit f)
negateOverLitVal _ = panic "negateOverLitVal: argument is not a number"
