{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Core where

import CSlash.Cs.Pass
import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Core.Type
import CSlash.Core.Kind
import {-# SOURCE #-} CSlash.Core.Subst
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

data Expr bLam bLet
  = Var CoreId
  | Lit Literal
  | App (Expr bLam bLet) (Arg bLam bLet)
  | Lam bLam (Maybe (MonoKind Zk)) (Expr bLam bLet) -- can bind term, type, or kind vars ('Just kind' if b is a term)
  -- Cant move the 'Maybe MonoKind' to 'CoreBndr.Id' since CoreBndr is used for case and other binding sites. 
  | Let (Bind bLam bLet) (Expr bLam bLet)
  | Case (Expr bLam bLet) bLet (Type Zk) [Alt bLam bLet]
  | Cast (Expr bLam bLet) (TypeCoercion Zk)
  | Tick CoreTickish (Expr bLam bLet)
  -- below are used as 'Arg's (from CsWrappers)
  | Type (Type Zk)
  | KiCo (KindCoercion Zk)
  | Kind (MonoKind Zk)
  deriving Data

type Arg = Expr 

data Alt bLam bLet = Alt AltCon [bLet] (Expr bLam bLet)
  deriving (Data)

data AltCon
  = DataAlt (DataCon Zk)
  | LitAlt Literal
  | DEFAULT
  deriving (Eq, Data)

-- We replace 'b' with 'CoreId' as the binder.
-- This removes 'type lets' that are present (but a pain) in GHC.
-- The situations where GHC finds a 'type let' useful do not occur in CSL.
data Bind bLam bLet
  = NonRec bLet (Expr bLam bLet)
  | Rec [(bLet, (Expr bLam bLet))]
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
        
needSaturated :: Bool
needSaturated = False

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

expandUnfolding_maybe :: Unfolding -> Maybe CoreExpr
expandUnfolding_maybe (CoreUnfolding { uf_cache = cache, uf_tmpl = rhs })
  | uf_expandable cache
  = Just rhs
expandUnfolding_maybe _ = Nothing

isCompulsoryUnfolding :: Unfolding -> Bool
isCompulsoryUnfolding (CoreUnfolding { uf_src = src }) = isCompulsorySource src
isCompulsoryUnfolding _ = False

isStableUnfolding :: Unfolding -> Bool
isStableUnfolding (CoreUnfolding { uf_src = src }) = isStableSource src
isStableUnfolding _ = False

hasSomeUnfolding :: Unfolding -> Bool
hasSomeUnfolding NoUnfolding = False
hasSomeUnfolding _ = True

neverUnfoldGuidance :: UnfoldingGuidance -> Bool
neverUnfoldGuidance UnfNever = True
neverUnfoldGuidance _ = False

canUnfold :: Unfolding -> Bool
canUnfold (CoreUnfolding { uf_guidance = g }) = not (neverUnfoldGuidance g)
canUnfold _ = False

{- *********************************************************************
*                                                                      *
             AltCon
*                                                                      *
********************************************************************* -}

instance Outputable AltCon where
  ppr (DataAlt dc) = ppr dc
  ppr (LitAlt lit) = ppr lit
  ppr DEFAULT = text "__DEFAULT"

cmpAltCon :: AltCon -> AltCon -> Ordering
cmpAltCon DEFAULT DEFAULT = EQ
cmpAltCon DEFAULT _ = LT
cmpAltCon (DataAlt d1) (DataAlt d2) = dataConTag d1 `compare` dataConTag d2
cmpAltCon (DataAlt _) DEFAULT = GT
cmpAltCon (LitAlt l1) (LitAlt l2) = l1 `compare` l2
cmpAltCon (LitAlt _) DEFAULT = GT
cmpAltCon con1 con2 = pprPanic "cmpAltCon" (ppr con1 $$ ppr con2)

{- *********************************************************************
*                                                                      *
            Useful synonyms
*                                                                      *
********************************************************************* -}

type CoreProgram = [CoreBind]

type CoreBndr = CoreBndrP Zk
data CoreBndrP p
  = Id (Id p)
  | Tv (TyVar p)
  | KCv (KiCoVar p)
  | Kv (KiVar p)

type CoreExpr = Expr CoreBndr CoreId

type CoreArg = Arg CoreBndr CoreId

type CoreBind = Bind CoreBndr CoreId

type CoreAlt = Alt CoreBndr CoreId

type CoreId = Id Zk
type CoreType = Type Zk
type CoreKind = Kind Zk
type CoreMonoKind = MonoKind Zk
type CoreVarSets = (IdSet Zk, TyCoVarSet Zk, TyVarSet Zk, KiCoVarSet Zk, KiVarSet Zk)

{- *********************************************************************
*                                                                      *
            Core-constructing functions with checking
*                                                                      *
********************************************************************* -}

mkLetRec :: [(b2, Expr b1 b2)] -> Expr b1 b2 -> Expr b1 b2
mkLetRec [] body = body
mkLetRec bs body = Let (Rec bs) body

varToCoreExpr :: CoreId -> Expr b1 b2
varToCoreExpr = Var

{- *********************************************************************
*                                                                      *
            Core-constructing functions with checking
*                                                                      *
********************************************************************* -}

collectArgs :: Expr b1 b2 -> (Expr b1 b2, [Arg b1 b2])
collectArgs expr = go expr []
  where
    go (App f a) as = go f (a:as)
    go e as = (e, as)

{- *********************************************************************
*                                                                      *
            Simple access functions
*                                                                      *
********************************************************************* -}

rhssOfBind :: Bind b1 b2 -> [Expr b1 b2]
rhssOfBind (NonRec _ rhs) = [rhs]
rhssOfBind (Rec pairs) = snd <$> pairs

rhssOfAlts :: [Alt b1 b2] -> [Expr b1 b2]
rhssOfAlts alts = [e | Alt _ _ e <- alts]

flattenBinds :: [Bind b1 b2] -> [(b2, Expr b1 b2)]
flattenBinds (NonRec b r : binds) = (b, r) : flattenBinds binds
flattenBinds (Rec prs1 : binds) = prs1 ++ flattenBinds binds
flattenBinds [] = []

collectBinders :: Expr b1 b2 -> ([b1], Expr b1 b2)
collectBinders expr = go [] expr
  where
    go bs (Lam b _ e) = go (b:bs) e
    go bs e = (reverse bs, e)

collectArgsTicks :: (CoreTickish -> Bool) -> Expr b1 b2 -> (Expr b1 b2, [Arg b1 b2], [CoreTickish])
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

isRuntimeVar :: CoreBndr -> Bool
isRuntimeVar Id {} = True
isRuntimeVar _ = False

isRuntimeArg :: CoreExpr -> Bool
isRuntimeArg = isValArg

isValArg :: Expr b1 b2 -> Bool
isValArg Type {} = False
isValArg Kind {} = False
isValArg KiCo {} = False -- Different from GHC; TODO: check for consistency/correctness
isValArg _ = True

isNonValArg :: Expr b1 b2 -> Bool
isNonValArg = not . isValArg

valArgCount :: [Arg b1 b2] -> Int
valArgCount = count isValArg

isJoinIdBndr :: CoreBndr -> Bool
isJoinIdBndr (Id id) = isJoinId id
isJoinIdBndr _ = False

{- *********************************************************************
*                                                                      *
            In/Out type synonyms
*                                                                      *
********************************************************************* -}

type InId = CoreId
type InVar = CoreBndr 
type InBind = CoreBind
type InExpr = CoreExpr

type OutId = CoreId
type OutVar = CoreBndr 
type OutBind = CoreBind
type OutExpr = CoreExpr

{- *********************************************************************
*                                                                      *
            Rewrite rules
*                                                                      *
********************************************************************* -}

data InScopeEnv = ISE TermSubstInScope IdUnfoldingFun

type IdUnfoldingFun = CoreId -> Unfolding
