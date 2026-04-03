{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Core
  ( module CSlash.Core
  , isStableSource
  ) where

import Prelude hiding ((<>))

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

unfoldingTemplate :: Unfolding -> CoreExpr
unfoldingTemplate = uf_tmpl

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

hasCoreUnfolding :: Unfolding -> Bool
hasCoreUnfolding CoreUnfolding{} = True
hasCoreUnfolding _ = False

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

isId :: CoreBndrP p -> Bool
isId (Id _) = True
isId _ = False

type CoreExpr = Expr CoreBndr CoreId

type CoreArg = Arg CoreBndr CoreId

type CoreBind = Bind CoreBndr CoreId

type CoreAlt = Alt CoreBndr CoreId

type CoreId = Id Zk
type CoreTyVar = TyVar Zk
type CoreKiCoVar = KiCoVar Zk
type CoreKiVar = KiVar Zk

type CoreType = Type Zk
type CoreKind = Kind Zk
type CoreMonoKind = MonoKind Zk
type CoreVarSets = (IdSet Zk, TyCoVarSet Zk, TyVarSet Zk, KiCoVarSet Zk, KiVarSet Zk)

{- *********************************************************************
*                                                                      *
            Tagging
*                                                                      *
********************************************************************* -}

data TaggedBndr b t = TB b t

type TaggedLetBndr = TaggedBndr CoreId
type TaggedLamBndr = TaggedBndr CoreBndr

type TaggedBind t = Bind (TaggedLamBndr t) (TaggedLetBndr t)
type TaggedExpr t = Expr (TaggedLamBndr t) (TaggedLetBndr t)
type TaggedArg t = Arg (TaggedLamBndr t) (TaggedLetBndr t)
type TaggedAlt t = Alt (TaggedLamBndr t) (TaggedLetBndr t)

instance (Outputable b, Outputable t) => Outputable (TaggedBndr b t) where
  ppr (TB b l) = char '<' <> ppr b <> comma <> ppr l <> char '>'

deTagExpr :: TaggedExpr t -> CoreExpr
deTagExpr (Var v) = Var v
deTagExpr (Lit l) = Lit l
deTagExpr (Type ty) = Type ty
deTagExpr (KiCo co) = KiCo co
deTagExpr (Kind ki) = Kind ki
deTagExpr (App e1 e2) = App (deTagExpr e1) (deTagExpr e2)
deTagExpr (Lam (TB b _) k e) = Lam b k (deTagExpr e)
deTagExpr (Let bind body) = Let (deTagBind bind) (deTagExpr body)
deTagExpr (Case e (TB b _) ty alts) = Case (deTagExpr e) b ty (map deTagAlt alts)
deTagExpr (Tick t e) = Tick t (deTagExpr e)
deTagExpr (Cast e co) = Cast (deTagExpr e) co

deTagBind :: TaggedBind t -> CoreBind
deTagBind (NonRec (TB b _) rhs) = NonRec b (deTagExpr rhs)
deTagBind (Rec prs) = Rec [(b, deTagExpr rhs) | (TB b _, rhs) <- prs]

deTagAlt :: TaggedAlt t -> CoreAlt
deTagAlt (Alt con bndrs rhs) = Alt con [b | TB b _ <- bndrs] (deTagExpr rhs)

{- *********************************************************************
*                                                                      *
            Core-constructing functions with checking
*                                                                      *
********************************************************************* -}

mkVarApps :: Expr b1 b2 -> [CoreId] -> Expr b1 b2
mkVarApps f vars = foldl' (\e a -> App e (varToCoreExpr a)) f vars

mkAbsVarApps :: Expr b1 b2 -> [(CoreBndr, a)] -> Expr b1 b2
mkAbsVarApps = foldl' (\e (a, _) -> case a of
                                            Id v -> App e (varToCoreExpr v)
                                            Tv v -> App e (Type (mkTyVarTy v))
                                            KCv v -> App e (KiCo (mkKiCoVarCo v))
                                            Kv v -> App e (Kind (mkKiVarKi v)))


mkLetRec :: [(b2, Expr b1 b2)] -> Expr b1 b2 -> Expr b1 b2
mkLetRec [] body = body
mkLetRec bs body = Let (Rec bs) body

varToCoreExpr :: CoreId -> Expr b1 b2
varToCoreExpr = Var

{- *********************************************************************
*                                                                      *
            Simple access functions
*                                                                      *
********************************************************************* -}

bindersOf :: Bind b1 b2 -> [b2]
bindersOf (NonRec binder _) = [binder]
bindersOf (Rec pairs) = fst <$> pairs

{-# INLINE foldBindersOfBindStrict #-}
foldBindersOfBindStrict :: (a -> b -> a) -> a -> Bind bLam b -> a
foldBindersOfBindStrict f = \z bind -> case bind of
  NonRec b _ -> f z b
  Rec pairs -> foldl' f z $ map fst pairs

{-# INLINE foldBindersOfBindsStrict #-}
foldBindersOfBindsStrict :: (a -> b -> a) -> a -> [Bind bLam b] -> a
foldBindersOfBindsStrict f = \z binds -> foldl' fold_bind z binds
  where
    fold_bind = foldBindersOfBindStrict f

rhssOfBind :: Bind b1 b2 -> [Expr b1 b2]
rhssOfBind (NonRec _ rhs) = [rhs]
rhssOfBind (Rec pairs) = snd <$> pairs

rhssOfAlts :: [Alt b1 b2] -> [Expr b1 b2]
rhssOfAlts alts = [e | Alt _ _ e <- alts]

flattenBinds :: [Bind b1 b2] -> [(b2, Expr b1 b2)]
flattenBinds (NonRec b r : binds) = (b, r) : flattenBinds binds
flattenBinds (Rec prs1 : binds) = prs1 ++ flattenBinds binds
flattenBinds [] = []

collectBinders :: Expr b1 b2 -> ([(b1, Maybe CoreMonoKind)], Expr b1 b2)
collectBinders expr = go [] expr
  where
    go bs (Lam b mki e) = go ((b, mki) : bs) e
    go bs e = (reverse bs, e)

collectNBinders :: JoinArity -> Expr b1 b2 -> ([(b1, Maybe CoreMonoKind)], Expr b1 b2)
collectNBinders orig_n orig_expr
  = go orig_n [] orig_expr
  where
    go 0 bs expr = (reverse bs, expr)
    go n bs (Lam b mki e) = go (n - 1) ((b, mki) : bs) e
    go _ _ _ = pprPanic "collectNBinders" $ int orig_n

collectArgs :: Expr b1 b2 -> (Expr b1 b2, [Arg b1 b2])
collectArgs expr = go expr []
  where
    go (App f a) as = go f (a:as)
    go e as = (e, as)

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

isCoBndr :: CoreBndr -> Bool
isCoBndr KCv {} = True
isCoBndr Id {} = False
isCoBndr Tv {} = False
isCoBndr Kv {} = False

isRuntimeArg :: CoreExpr -> Bool
isRuntimeArg = isValArg

runtimeVar_maybe :: CoreBndr -> Maybe CoreId
runtimeVar_maybe (Id id) = Just id
runtimeVar_maybe _ = Nothing

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
            Annotated core
*                                                                      *
********************************************************************* -}

type AnnExpr lamBndr letBndr annot = (annot, AnnExpr' lamBndr letBndr annot)

data AnnExpr' lamBndr letBndr annot
  = AnnVar CoreId
  | AnnLit Literal
  | AnnLam lamBndr (Maybe (annot, CoreMonoKind)) (AnnExpr lamBndr letBndr annot)
  | AnnApp (AnnExpr lamBndr letBndr annot) (AnnExpr lamBndr letBndr annot)
  | AnnCase (AnnExpr lamBndr letBndr annot) letBndr CoreType [AnnAlt lamBndr letBndr annot]
  | AnnLet (AnnBind lamBndr letBndr annot) (AnnExpr lamBndr letBndr annot)
  | AnnCast (AnnExpr lamBndr letBndr annot) (annot, TypeCoercion Zk)
  | AnnTick CoreTickish (AnnExpr lamBndr letBndr annot)
  | AnnType CoreType
  | AnnKiCo (KindCoercion Zk)
  | AnnKind CoreMonoKind

data AnnAlt lamBndr letBndr annot = AnnAlt AltCon [letBndr] (AnnExpr lamBndr letBndr annot)

data AnnBind lamBndr letBndr annot
  = AnnNonRec letBndr (AnnExpr lamBndr letBndr annot)
  | AnnRec [(letBndr, AnnExpr lamBndr letBndr annot)]

collectAnnArgs :: AnnExpr b1 b2 a -> (AnnExpr b1 b2 a, [AnnExpr b1 b2 a])
collectAnnArgs expr
  = go expr []
  where
    go (_, AnnApp f a) as = go f (a:as)
    go e as = (e, as)

collectAnnBndrs :: AnnExpr b1 b2 a -> ([(b1, Maybe CoreMonoKind)], AnnExpr b1 b2 a)
collectAnnBndrs e = collect [] e
  where
    collect bs (_, AnnLam b mk body) = collect ((b, k) : bs) body
      where k = case mk of
                  Just (_, k) -> Just k
                  _ -> Nothing
    collect bs body = (reverse bs, body)

collectNAnnBndrs :: Int -> AnnExpr b1 b2 a -> ([(b1, Maybe CoreMonoKind)], AnnExpr b1 b2 a)
collectNAnnBndrs orig_n e
  = collect orig_n [] e
  where
    collect 0 bs body = (reverse bs, body)
    collect n bs (_, AnnLam b mk body) = collect (n - 1) ((b, k) : bs) body
      where k = case mk of
                  Just (_, k) -> Just k
                  _ -> Nothing
    collect _ _ _ = pprPanic "collectNAnnBnders" $ int orig_n

deAnnotate :: AnnExpr b1 b2 a -> Expr b1 b2
deAnnotate (_, e) = deAnnotate' e

deAnnotate' :: AnnExpr' b1 b2 a -> Expr b1 b2
deAnnotate' (AnnType t) = Type t
deAnnotate' (AnnKiCo co) = KiCo co
deAnnotate' (AnnKind ki) = Kind ki
deAnnotate' (AnnVar v) = Var v
deAnnotate' (AnnLit lit) = Lit lit
deAnnotate' (AnnLam binder Nothing body) = Lam binder Nothing (deAnnotate body)
deAnnotate' (AnnLam binder (Just (_, ki))  body) = Lam binder (Just ki) (deAnnotate body)
deAnnotate' (AnnApp fun arg) = App (deAnnotate fun) (deAnnotate arg)
deAnnotate' (AnnCast e (_, co)) = Cast (deAnnotate e) co
deAnnotate' (AnnTick tick body) = Tick tick (deAnnotate body)
deAnnotate' (AnnLet bind body)
  = Let (deAnnBind bind) (deAnnotate body)
deAnnotate' (AnnCase scrut v t alts)
  = Case (deAnnotate scrut) v t (map deAnnAlt alts)

deAnnAlt :: AnnAlt b1 b2 a -> Alt b1 b2
deAnnAlt (AnnAlt con args rhs) = Alt con args (deAnnotate rhs)

deAnnBind :: AnnBind b1 b2 a -> Bind b1 b2
deAnnBind (AnnNonRec var rhs) = NonRec var (deAnnotate rhs)
deAnnBind (AnnRec pairs) = Rec [(v, deAnnotate rhs) | (v, rhs) <- pairs]

{- *********************************************************************
*                                                                      *
            In/Out type synonyms
*                                                                      *
********************************************************************* -}

type InId = CoreId
type InBndr = CoreBndr
type InBind = CoreBind
type InExpr = CoreExpr

type OutId = CoreId
type OutBndr = CoreBndr
type OutBind = CoreBind
type OutExpr = CoreExpr

{- *********************************************************************
*                                                                      *
            Rewrite rules
*                                                                      *
********************************************************************* -}

data InScopeEnv = ISE TermSubstInScope IdUnfoldingFun

type IdUnfoldingFun = CoreId -> Unfolding
