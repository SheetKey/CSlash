module CSlash.Utils.Lexeme
  ( isLexSym
  , isLexDConSym
  , isLexTyConSym
  , isLexVarSym
  , isLexKdSym
  ) where

import qualified GHC.Utils.Lexeme as X

import CSlash.Data.FastString

isLexSym :: FastString -> Bool
isLexSym cs = isLexDConSym cs || isLexVarSym cs || isLexKdSym cs

isLexDConSym :: FastString -> Bool
isLexDConSym = X.isLexConSym

isLexTyConSym :: FastString -> Bool
isLexTyConSym = isLexVarSym

isLexVarSym :: FastString -> Bool
isLexVarSym = X.isLexVarSym

isLexKdSym :: FastString -> Bool
isLexKdSym  cs = case unpackFS cs of
  [c] -> c == '★' || c == '●' || c == '○'
  _ -> False
