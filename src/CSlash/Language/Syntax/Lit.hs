module CSlash.Language.Syntax.Lit where

import CSlash.Language.Syntax.Extension

import CSlash.Types.SourceText

import CSlash.Data.FastString

data CsLit x
  = CsChar (XCsChar x) {- SourceText -} Char
  | CsString (XCsString x) {- SourceText -} FastString
  | CsInt (XCsInt x) IntegralLit
  | CsDouble (XCsDouble x) FractionalLit
