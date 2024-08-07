{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Core where

import CSlash.Types.Var
import CSlash.Core.Type
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Literal
import CSlash.Types.Tickish
import CSlash.Core.DataCon
import CSlash.Unit.Module
import CSlash.Types.Basic
import CSlash.Types.Unique.Set

import CSlash.Utils.Binary
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Data.Data hiding (TyCon)
import Data.Int
import Data.Word

{- *********************************************************************
*                                                                      *
            The main data types
*                                                                      *
********************************************************************* -}

data Expr b
  = Var Id
  | Lit Literal
  | App (Expr b) (Arg b)
  | Lam b (Expr b)
  | Let (Bind b) (Expr b)
  | Case (Expr b) b Type [Alt b]
  deriving Data

type Arg b = Expr b

data Alt b = Alt AltCon [b] (Expr b)
  deriving (Data)

data AltCon
  = DataAlt DataCon
  | LitAlt Literal
  | DEFAULT
  deriving (Eq, Data)

data Bind b
  = NonRec b (Expr b)
  | Rec [(b, (Expr b))]
  deriving Data

{- *********************************************************************
*                                                                      *
                Unfoldings
*                                                                      *
********************************************************************* -}

data Unfolding
  = NoUnfolding
  | OtherCon [AltCon]

noUnfolding :: Unfolding
noUnfolding = NoUnfolding

evaldUnfolding :: Unfolding
evaldUnfolding = OtherCon []

isEvaldUnfolding :: Unfolding -> Bool
isEvaldUnfolding (OtherCon _) = True
isEvaldUnfolding NoUnfolding = False
  
{- *********************************************************************
*                                                                      *
            Useful synonyms
*                                                                      *
********************************************************************* -}

type CoreProgram = [CoreBind]

type CoreBndr = Var

type CoreExpr = Expr CoreBndr

type CoreBind = Bind CoreBndr
