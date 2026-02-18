{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Core where

import CSlash.Cs.Pass
import CSlash.Types.Var
import CSlash.Core.Type
import CSlash.Core.Kind
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
  = Var (Id Zk)
  | Lit Literal
  | App (Expr b) (Arg b)
  | Lam b (Maybe (MonoKind Zk)) (Expr b) -- can bind term, type, or kind vars ('Just kind' if b is a term)
  | Let (Bind b) (Expr b)
  | Case (Expr b) b (Type Zk) [Alt b]
  | Cast (Expr b) (TypeCoercion Zk)
  | Tick CoreTickish (Expr b)
  -- below are used as 'Arg's (from CsWrappers)
  | Type (Type Zk)
  | KiCo (KindCoercion Zk)
  | Kind (MonoKind Zk)
  deriving Data

type Arg b = Expr b

data Alt b = Alt AltCon [b] (Expr b)
  deriving (Data)

data AltCon
  = DataAlt (DataCon Zk)
  | LitAlt Literal
  | DEFAULT
  deriving (Eq, Data)

data Bind b
  = NonRec b (Expr b)
  | Rec [(b, (Expr b))]
  deriving Data

instance Outputable AltCon where
  ppr (DataAlt dc) = ppr dc
  ppr (LitAlt lit) = ppr lit
  ppr DEFAULT = text "__DEFAULT"

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

isConLikeUnfolding :: Unfolding -> Bool
isConLikeUnfolding (CoreUnfolding { uf_cache = cache }) = uf_is_conlike cache
isConLikeUnfolding _ = False

hasSomeUnfolding :: Unfolding -> Bool
hasSomeUnfolding NoUnfolding = False
hasSomeUnfolding _ = True
  
{- *********************************************************************
*                                                                      *
            Useful synonyms
*                                                                      *
********************************************************************* -}

type CoreProgram = [CoreBind]

data CoreBndr p
  = Id (Id p)
  | Tv (TyVar p)
  | KCv (KiCoVar p)
  | Kv (KiVar p)

type CoreExpr = Expr (CoreBndr Zk)

type CoreArg = Arg (CoreBndr Zk)

type CoreBind = Bind (CoreBndr Zk)
  
{- *********************************************************************
*                                                                      *
            Core-constructing functions with checking
*                                                                      *
********************************************************************* -}

varToCoreExpr :: CoreBndr Zk -> Expr b
varToCoreExpr v = panic "varToCoreExpr"

{- *********************************************************************
*                                                                      *
            Core-constructing functions with checking
*                                                                      *
********************************************************************* -}

collectArgs :: Expr b -> (Expr b, [Arg b])
collectArgs expr = go expr []
  where
    go (App f a) as = go f (a:as)
    go e as = (e, as)

{- *********************************************************************
*                                                                      *
            Simple access functions
*                                                                      *
********************************************************************* -}

collectArgsTicks :: (CoreTickish -> Bool) -> Expr b -> (Expr b, [Arg b], [CoreTickish])
collectArgsTicks skipTick expr = go expr [] []
  where go (App f a) as ts = go f (a:as) ts
        go (Tick t e) as ts
          | skipTick t = go e as (t:ts)
        go e as ts = (e, as, reverse ts)

{- *********************************************************************
*                                                                      *
            Predicates
*                                                                      *
********************************************************************* -}

isRuntimeVar :: CoreBndr p -> Bool
isRuntimeVar Id {} = True
isRuntimeVar _ = False

isRuntimeArg :: CoreExpr -> Bool
isRuntimeArg = isValArg

isValArg :: Expr b -> Bool
isValArg Type {} = False
isValArg Kind {} = False
isValArg KiCo {} = False -- Different from GHC; TODO: check for consistency/correctness
isValArg _ = True

isNonValArg :: CoreExpr -> Bool
isNonValArg = not . isValArg

valArgCount :: [Arg b] -> Int
valArgCount = count isValArg

{- *********************************************************************
*                                                                      *
            In/Out type synonyms
*                                                                      *
********************************************************************* -}

type InId = Id Zk
type InExpr = CoreExpr

type OutId = Id Zk
type OutExpr = CoreExpr
