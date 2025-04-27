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
  | CoreUnfolding
    { uf_tmpl :: CoreExpr
    , uf_src :: UnfoldingSource
    , uf_is_top :: Bool
    , uf_cache :: UnfoldingCache
    , uf_guidance :: UnfoldingGuidance
    }

data UnfoldingCache = UnfoldingCache
  { uf_is_value :: !Bool
  , uf_is_conlike :: !Bool
  , uf_is_work_free :: !Bool
  , uf_expandable :: !Bool
  }
  deriving Eq

data UnfoldingGuidance
  = UnfWhen
    { ug_arity :: Arity
    , ug_unsat_ok :: Bool
    , ug_boring_ok :: Bool
    }
  | UnfIfGoodArgs
    { ug_args :: [Int]
    , ug_size :: Int
    , ug_res :: Int
    }
  | UnfNever
  deriving Eq
        

noUnfolding :: Unfolding
noUnfolding = NoUnfolding

evaldUnfolding :: Unfolding
evaldUnfolding = OtherCon []

isEvaldUnfolding :: Unfolding -> Bool
isEvaldUnfolding (OtherCon _) = True
isEvaldUnfolding NoUnfolding = False
isEvaldUnfolding (CoreUnfolding { uf_cache = cache }) = uf_is_value cache
  
{- *********************************************************************
*                                                                      *
            Useful synonyms
*                                                                      *
********************************************************************* -}

type CoreProgram = [CoreBind]

type CoreBndr = Var

type CoreExpr = Expr CoreBndr

type CoreBind = Bind CoreBndr
