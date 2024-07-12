module CSlash.Utils.Lexeme
  ( X.isLexCon
  , isLexSym
  , X.isLexConSym
  , X.isLexVarSym

  , isLexKdSym
  ) where

import qualified GHC.Utils.Lexeme as X

import CSlash.Data.FastString

isLexSym :: FastString -> Bool
isLexSym cs = X.isLexSym cs || isLexKdSym cs

isLexKdSym :: FastString -> Bool
isLexKdSym  cs = case unpackFS cs of
  [c] -> c == '★' || c == '●' || c == '○'
  _ -> False
