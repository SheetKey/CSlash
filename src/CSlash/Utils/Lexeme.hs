module CSlash.Utils.Lexeme
  ( isLexSym
  , isLexDConSym
  , isLexTyConSym
  , isLexVarSym
  ) where

import qualified GHC.Utils.Lexeme as X

import CSlash.Data.FastString
import Data.Char
import qualified Data.Set as Set

isLexSym :: FastString -> Bool
isLexSym cs = isLexDConSym cs || isLexVarSym cs

isLexDConSym :: FastString -> Bool
isLexDConSym = X.isLexConSym

isLexTyConSym :: FastString -> Bool
isLexTyConSym = isLexVarSym

isLexVarSym :: FastString -> Bool
isLexVarSym = X.isLexVarSym
