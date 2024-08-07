{-# LANGUAGE MagicHash #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Types.Literal where

import CSlash.Utils.Outputable

import Data.Data
import GHC.Exts (isTrue#, dataToTag#, (<#))
import Numeric (fromRat)

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

instance Eq Literal where
  a == b = compare a b == EQ

instance Ord Literal where
  compare = cmpLit

cmpLit :: Literal -> Literal -> Ordering
cmpLit (LitChar a) (LitChar b) = a `compare` b
cmpLit LitNullAddr LitNullAddr = EQ
cmpLit (LitFloat a) (LitFloat b) = a `compare` b
cmpLit (LitDouble a) (LitDouble b) = a `compare` b
cmpLit (LitNumber nt1 a) (LitNumber nt2 b)
  = (nt1 `compare` nt2) `mappend` (a `compare` b)
cmpLit lit1 lit2
  | isTrue# (dataToTag# lit1 <# dataToTag# lit2) = LT
  | otherwise = GT

pprLiteral :: (SDoc -> SDoc) -> Literal -> SDoc
pprLiteral _ (LitChar c) = pprCsChar c
pprLiteral _ LitNullAddr = text "__NULL"
pprLiteral _ (LitFloat f) = float (fromRat f)
pprLiteral _ (LitDouble d) = double (fromRat d)
pprLiteral _ (LitNumber nt i)
  = case nt of
      LitNumInt _ -> integer i
      LitNumWord _ -> word i
