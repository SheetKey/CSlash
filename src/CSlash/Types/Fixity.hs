{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Types.Fixity where

import CSlash.Utils.Outputable
import CSlash.Utils.Binary

import Data.Data hiding (Fixity, Prefix, Infix)

data Fixity = Fixity Int FixityDirection
  deriving Data

instance Outputable Fixity where
  ppr (Fixity prec dir) = hcat [ppr dir, space, int prec]

instance Eq Fixity where
  (Fixity p1 dir1) == (Fixity p2 dir2) = p1 == p2 && dir1 == dir2

instance Binary Fixity where
    put_ bh (Fixity aa ab) = do
            put_ bh aa
            put_ bh ab
    get bh = do
          aa <- get bh
          ab <- get bh
          return (Fixity aa ab)

data FixityDirection
  = InfixL
  | InfixR
  | InfixN
  deriving (Eq, Data)

instance Outputable FixityDirection where
  ppr InfixL = text "infixl"
  ppr InfixR = text "infixr"
  ppr InfixN = text "infix"

instance Binary FixityDirection where
  put_ bh InfixL = putByte bh 0
  put_ bh InfixR = putByte bh 1
  put_ bh InfixN = putByte bh 2
  get bh = do
    h <- getByte bh
    case h of
      0 -> return InfixL
      1 -> return InfixR
      _ -> return InfixN

maxPrecedence :: Int
maxPrecedence = 9

minPrecedence :: Int
minPrecedence = 0

defaultFixity :: Fixity
defaultFixity = Fixity maxPrecedence InfixL

negateFixity :: Fixity
negateFixity = Fixity 6 InfixL

funTyFixity :: Fixity
funTyFixity = Fixity (-1) InfixR

compareFixity :: Fixity -> Fixity -> (Bool, Bool)
compareFixity (Fixity prec1 dir1) (Fixity prec2 dir2)
  = case prec1 `compare` prec2 of
      GT -> left
      LT -> right
      EQ -> case (dir1, dir2) of
              (InfixR, InfixR) -> right
              (InfixL, InfixL) -> left
              _ -> error_please
  where
    right = (False, True)
    left = (False, False)
    error_please = (True, False)

data LexicalFixity = Prefix | Infix deriving (Data, Eq)

instance Outputable LexicalFixity where
  ppr Prefix = text "Prefix"
  ppr Infix  = text "Infix"
