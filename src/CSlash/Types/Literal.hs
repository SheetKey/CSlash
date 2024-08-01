module CSlash.Types.Literal where

import CSlash.Utils.Outputable

import Data.Data

data Literal
  = LitChar Char
  | LitNumber !LitNumType !Integer
  | LitNullAddr
  | LitFloat Rational
  | LitDouble Rational
  deriving Data

-- we allow arbitrary precision
data LitNumType
  = LitNumInt Int
  | LitNumWord Int
  deriving (Data, Eq, Ord)

instance Outputable Literal where
  ppr = pprLiteral id

pprLiteral :: (SDoc -> SDoc) -> Literal -> SDoc
pprLiteral _ (LitChar c) = pprCsChar c
pprLiteral _ LitNullAddr = text "__NULL"
pprLiteral _ (LitFloat f) = float (fromRat f)
pprLiteral _ (LitDouble d) = double (fromRat d)
pprLiteral _ (LitNumber nt i)
  = case nt of
      LitNumInt _ -> integer i
      LitNummWord _ -> word i
