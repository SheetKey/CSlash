{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Rep where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import {-# SOURCE #-} CSlash.Core.Type.FVs
import {-# SOURCE #-} CSlash.Core.Subst
import CSlash.Core.TyCon

import CSlash.Types.Var.TyVar
import CSlash.Types.Var.KiVar
import CSlash.Types.Var.CoVar
import CSlash.Types.Var.Class
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env

import CSlash.Types.Basic
import CSlash.Types.Unique
import CSlash.Types.Name

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.FV

import CSlash.Data.FastString
import CSlash.Data.Pair

import qualified Data.Data as Data hiding (TyCon)
import Data.IORef (IORef)

{- **********************************************************************
*                                                                       *
                        Type
*                                                                       *
********************************************************************** -}

data Type p 
  = TyVarTy (TyVar p)
  | AppTy (Type p) (Type p) -- The first arg must be an 'AppTy' or a 'TyVarTy' or a 'TyLam'
  | TyLamTy (TyVar p) (Type p) -- Used for TySyns, NOT in the types of DataCons (only Foralls)
  | BigTyLamTy (KiVar p) (Type p) -- Could add a field for 'ForAllKi', then this would ONLY be for TySyns (maybe)
  | TyConApp (TyCon p) [Type p]
  | ForAllTy !(ForAllBinder (TyVar p)) (Type p)
  | ForAllKiCo !(KiCoVar p) (Type p)
  | FunTy
    { ft_kind :: MonoKind p
    , ft_arg :: Type p
    , ft_res :: Type p
    }
  | LocalTyRow Name (MonoKind p)
  | SetRowsTy (Type p) [SetRow p]
  | CastTy (Type p) (KindCoercion p)
  | Embed (MonoKind p) -- for application to a 'BigTyLamTy
  | KindCoercion (KindCoercion p) -- embed a kind coercion (evidence stuff)
  deriving Data.Data

data SetRow p
  = SetRowVal Name -- (Expr p)
  | SetRowTy Name (Type p)
  deriving (Data.Data)

{- **********************************************************************
*                                                                       *
                        TypeCoercion
*                                                                       *
********************************************************************** -}

data TypeCoercion p where
  TyRefl :: Type p -> TypeCoercion p
  GRefl :: Type p -> KindCoercion p -> TypeCoercion p
  TyConAppCo :: TyCon p -> [TypeCoercion p] -> TypeCoercion p
  AppCo :: TypeCoercion p -> TypeCoercion p -> TypeCoercion p
  ForAllCo
    :: { tfco_tv :: TyVar p
       , tfco_visL :: !ForAllFlag
       , tfco_visR :: !ForAllFlag
       , tfco_tv_kind_co :: KindCoercion p
       , tfco_body :: TypeCoercion p }
    -> TypeCoercion p
  ForAllCoCo
    :: { tfcoco_kcv :: KiCoVar p
       , tfcoco_kcv_kind_co :: KindCoercion p
       , tfcoco_body :: TypeCoercion p }
    -> TypeCoercion p
  TyFunCo
    :: { tfco_ki :: KindCoercion p
       , tfco_arg :: TypeCoercion p
       , tfco_res :: TypeCoercion p
       }
    -> TypeCoercion p
  TyCoVarCo :: TyCoVar p -> TypeCoercion p
  LiftKCo :: KindCoercion p -> TypeCoercion p
  TySymCo :: TypeCoercion p -> TypeCoercion p
  TyTransCo :: TypeCoercion p -> TypeCoercion p -> TypeCoercion p
  LRCo :: LeftOrRight -> TypeCoercion p -> TypeCoercion p
  TyHoleCo :: TypeCoercionHole -> TypeCoercion Tc

data TypeCoercionHole = TypeCoercionHole
  { tch_co_var :: TcTyCoVar
  , tch_ref :: IORef (Maybe (TypeCoercion Tc))
  }

data MTypeCoercion p
  = MRefl
  | MCo (TypeCoercion p)
  deriving Data.Data

{- **********************************************************************
*                                                                       *
                        Kind
*                                                                       *
********************************************************************** -}

data Kind p
  = ForAllKi !(KiVar p) (Kind p)
  | Mono (MonoKind p)
  deriving Data.Data

data MonoKind p
  = KiVarKi (KiVar p)
  | BIKi BuiltInKi
  | KiPredApp KiPredCon (MonoKind p) (MonoKind p)
  | KiConApp (KiCon p)
  | FunKi
    { fk_f :: FunKiFlag
    , fk_arg :: MonoKind p
    , fk_res :: MonoKind p
    }
  deriving Data.Data

data BuiltInKi
  = UKd
  | AKd
  | LKd
  deriving (Show, Eq, Ord, Data.Data)

data KiPredCon
  = LTKi
  | LTEQKi
  | EQKi
  deriving (Show, Eq, Ord, Data.Data)

data KiCon p = KiCon
  { kicon_name :: Maybe Name
  , kicon_base :: MonoKind p
  , kicon_rows :: [RowSig p] -- NonEmpty
  }
  deriving Data.Data

-- All ki vars present here should be bound elsewhere.
-- I.e., we have the invariant that there are no 'ForAllKi's at the head
-- of a RowTySig, and no ForAlls at the head of a kid sig, guaranteed by 'MonoKind'
-- This is useful/necessary for handling kivars properly during checking/unification/solving.
-- The first part of the invariant may not be as necessary as the second, but still makes like easier.
data RowSig p
  = RowTySig Name (Type p)
  | RowKiSig Name (MonoKind p)
  deriving Data.Data

data FunKiFlag
  = FKF_K_K -- Kind -> Kind
  | FKF_C_K -- Constraint -> Kind
  deriving (Eq, Ord, Data.Data)

{- **********************************************************************
*                                                                       *
                        KindCoercion
*                                                                       *
********************************************************************** -}

data KindCoercion p where
  Refl :: (MonoKind p) -- refl : kv = kv
    -> KindCoercion p
  BI_U_A             -- builtin : u < a
    :: KindCoercion p
  BI_A_L             -- builtin : a < l
    :: KindCoercion p
  BI_U_LTEQ :: (MonoKind p)
    -> KindCoercion p
  BI_LTEQ_L :: (MonoKind p)
    -> KindCoercion p
  LiftEq :: (KindCoercion p) -- LiftEq : (kv = kv) -> (kv <= kv)
    -> KindCoercion p
  LiftLT :: (KindCoercion p) -- LiftLT : (kv1 < kv2) -> (kv1 <= kv2)
    -> KindCoercion p
  FunCo ::
    { fco_afl :: FunKiFlag
    , fco_afr :: FunKiFlag
    , fco_arg :: KindCoercion p
    , fco_res :: KindCoercion p }
    -> KindCoercion p
  -- KiPredAppCo :: KiPredCon -> KindCoercion p -> KindCoercion p -> KindCoercion p
  KiRowCo :: KindCoercion p -> [RowCoercion p] -> KindCoercion p
  KiCoVarCo :: (KiCoVar p) -> KindCoercion p
  SymCo :: (KindCoercion p) -> KindCoercion p
  TransCo :: (KindCoercion p) -> (KindCoercion p) -> KindCoercion p
  SelCo :: CoSel -> (KindCoercion p) -> KindCoercion p
  HoleCo :: KindCoercionHole -> KindCoercion Tc

data RowCoercion p
  = RowTySigCo Name (TypeCoercion p)
  | RowKiSigCo Name (KindCoercion p)
  deriving Data.Data

data KindCoercionHole = KindCoercionHole
  { kch_co_var :: TcKiCoVar
  , kch_ref :: IORef (Maybe (KindCoercion Tc))
  }

data CoSel
  = SelFun FunSel
  deriving Data.Data

data FunSel = SelArg | SelRes
  deriving Data.Data

{- **********************************************************************
*                                                                       *
                        Outputable instances
*                                                                       *
********************************************************************** -}

instance IsPass p => Outputable (Type (CsPass p)) where
  ppr = pprType

instance Outputable (TypeCoercion p) where
  ppr = const $ text "[TyCo]"

instance Outputable TypeCoercionHole where
  ppr = const $ text "[TyCoHole]"

instance Outputable (MTypeCoercion p) where
  ppr MRefl = text "MRefl"
  ppr (MCo co) = text "MCo" <+> ppr co

instance Outputable BuiltInKi where
  ppr UKd = uKindLit
  ppr AKd = aKindLit
  ppr LKd = lKindLit

instance Outputable KiPredCon where
  ppr LTKi = char '<'
  ppr LTEQKi = text "<="
  ppr EQKi = char '~'

instance IsPass p => Outputable (Kind (CsPass p)) where
  ppr = pprKind

instance IsPass p => Outputable (MonoKind (CsPass p)) where
  ppr = pprMonoKind

instance IsPass p => Outputable (RowSig (CsPass p)) where
  ppr = pprRowSig

instance IsPass p => Outputable (KiCon (CsPass p)) where
  ppr (KiCon nm base rows) = text "kind" <+> ppr nm <+> equals <+> ppr base <+> dot <> braces
    (fsep (punctuate comma (map ppr rows)))

instance Outputable FunKiFlag where
  ppr FKF_K_K = text "[->]"
  ppr FKF_C_K = text "[=>]"

instance Outputable CoSel where
  ppr (SelFun fs) = text "Fun" <> parens (ppr fs)

instance Outputable FunSel where
  ppr SelArg = text "arg"
  ppr SelRes = text "res"

instance IsPass p => Outputable (KindCoercion (CsPass p)) where
  ppr = pprKiCo

instance  Outputable KindCoercionHole where
  ppr (KindCoercionHole { kch_co_var = cv }) = braces (ppr cv)

{- **********************************************************************
*                                                                       *
                        Data instances
*                                                                       *
********************************************************************** -}

instance Data.Typeable p => Data.Data (TypeCoercion p)

instance Data.Data TypeCoercionHole

instance (Data.Typeable p) => Data.Data (KindCoercion p) where
  toConstr _ = abstractConstr "KindCoercion"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "KindCoercion"

instance Data.Data KindCoercionHole where
  toConstr _ = abstractConstr "KindCoercionHole"
  gunfold _ _ = error "gunfold"
  dataTypeOf _ = mkNoRepType "KindCoercionHole"

{- **********************************************************************
*                                                                       *
                        Uniquable instances
*                                                                       *
********************************************************************** -}

instance Uniquable TypeCoercionHole where
  getUnique (TypeCoercionHole { tch_co_var = cv }) = getUnique cv

instance Uniquable KindCoercionHole where
  getUnique (KindCoercionHole { kch_co_var = cv }) = getUnique cv

instance Uniquable BuiltInKi where
  getUnique kc = getUnique $ mkFastString $ show kc

instance Uniquable KiPredCon where
  getUnique pred = getUnique $ mkFastString $ show pred

{- **********************************************************************
*                                                                       *
                        Eq/Ord instances
*                                                                       *
********************************************************************** -}

instance Eq (MonoKind p) where
  k1 == k2 = go k1 k2
    where
      go (BIKi k1) (BIKi k2) = k1 == k2
      go (KiPredApp p1 ka1 kb1) (KiPredApp p2 ka2 kb2)
        = p1 == p2 && ka1 == ka2 && kb1 == kb2
      go (KiVarKi v) (KiVarKi v') = v == v'
      go (FunKi v1 k1 k2) (FunKi v1' k1' k2') = (v1 == v1') && go k1 k1' && go k2 k2'
      go _ _ = False

      gos [] [] = True
      gos (k1:ks1) (k2:ks2) = go k1 k2 && gos ks1 ks2
      gos _ _ = False

{- **********************************************************************
*                                                                       *
                        HasFVs instances
*                                                                       *
********************************************************************** -}

instance HasFVs (Type p) where
  type FVInScope (Type p) = (TyVarSet p, KiCoVarSet p, KiVarSet p)
  type FVAcc (Type p) = ([TyVar p], TyVarSet p, [KiCoVar p], KiCoVarSet p, [KiVar p], KiVarSet p)
  type FVArg (Type p) = E3 (TyVar p) (KiCoVar p) (KiVar p)

  fvElemAcc (In1 tv) (_, haveSet, _, _, _, _) = tv `elemVarSet` haveSet
  fvElemAcc (In2 kcv) (_, _, _, haveSet, _, _) = kcv `elemVarSet` haveSet
  fvElemAcc (In3 kv) (_, _, _, _, _, haveSet) = kv `elemVarSet` haveSet

  fvElemIS (In1 tv) (in_scope, _, _) = tv `elemVarSet` in_scope
  fvElemIS (In2 kcv) (_, in_scope, _) = kcv `elemVarSet` in_scope
  fvElemIS (In3 kv) (_, _, in_scope) = kv `elemVarSet` in_scope

  fvExtendAcc (In1 tv) (have, haveSet, kcs, kcset, ks, kset)
    = (tv:have, extendVarSet haveSet tv, kcs, kcset, ks, kset)
  fvExtendAcc (In2 kcv) (ts, tset, have, haveSet, ks, kset)
    = (ts, tset, kcv:have, extendVarSet haveSet kcv, ks, kset)
  fvExtendAcc (In3 kv) (ts, tset, kcs, kcset, have, haveSet)
    = (ts, tset, kcs, kcset, kv:have, extendVarSet haveSet kv)

  fvExtendIS (In1 tv) (in_scope, kcs, ks) = (extendVarSet in_scope tv, kcs, ks)
  fvExtendIS (In2 kcv) (ts, in_scope, ks) = (ts, extendVarSet in_scope kcv, ks)
  fvExtendIS (In3 kv) (ts, kcs, in_scope) = (ts, kcs, extendVarSet in_scope kv)

  fvEmptyAcc = ([], emptyVarSet, [], emptyVarSet, [], emptyVarSet)
  fvEmptyIS = (emptyVarSet, emptyVarSet, emptyVarSet)

instance HasFVs (Kind p) where
  type FVInScope (Kind p) = KiVarSet p
  type FVAcc (Kind p) = ([KiVar p], KiVarSet p)
  type FVArg (Kind p) = KiVar p

  fvElemAcc kv (_, haveSet) = kv `elemVarSet` haveSet
  fvElemIS kv in_scope = kv `elemVarSet` in_scope

  fvExtendAcc kv (have, haveSet) = (kv:have, extendVarSet haveSet kv)
  fvExtendIS kv in_scope = extendVarSet in_scope kv

  fvEmptyAcc = ([], emptyVarSet)
  fvEmptyIS = emptyVarSet

{- *********************************************************************
*                                                                      *
                Type representation
*                                                                      *
********************************************************************* -}

noView :: Type p -> Maybe (Type p)
noView _ = Nothing

rewriterView :: HasPass p pass => Type p -> Maybe (Type p)
rewriterView (TyConApp tc tys)
  | isTypeSynonymTyCon tc
  , isForgetfulSynTyCon tc
  = expandSynTyConApp_maybe tc tys
rewriterView ty@(AppTy{}) = expandTyLamApp_maybe ty isForgetfulTy
rewriterView _ = Nothing
{-# INLINE rewriterView #-}

coreView :: HasPass p pass => Type p -> Maybe (Type p)
coreView (TyConApp tc tys) = expandSynTyConApp_maybe tc tys
coreView ty@(AppTy{}) = expandTyLamApp_maybe ty (const True)
coreView _ = Nothing
{-# INLINE coreView #-}

coreFullView :: HasPass p pass => Type p -> Type p
coreFullView ty@(TyConApp tc _)
  | isTypeSynonymTyCon tc = core_full_view ty
coreFullView ty@(AppTy{}) = core_full_view ty
coreFullView ty = ty
{-# INLINE coreFullView #-}

core_full_view :: HasPass p pass => Type p -> Type p
core_full_view ty
  | Just ty' <- coreView ty = core_full_view ty'
  | otherwise = ty

expandTyLamApp_maybe :: HasPass p pass => Type p -> (Type p -> Bool) -> Maybe (Type p)
expandTyLamApp_maybe ty pred = case split ty [] of
  (fn, args)
    | let arity = tyFunArity fn
    , args `saturates` arity
    , pred fn
      -> Just $! (expand_syn fn args)
  _ -> Nothing
  where
    split (AppTy ty arg) args = split ty (arg:args)
    split ty args = (ty, args)

tyFunArity :: Type p -> Arity
tyFunArity = go 0
  where
    go i (TyLamTy _ ty) = go (i + 1) ty
    go i (BigTyLamTy _ ty) = go (i + 1) ty
    go i _ = i

expandSynTyConApp_maybe :: HasPass p pass => TyCon p -> [Type p] -> Maybe (Type p)
expandSynTyConApp_maybe tc arg_tys
  | Just rhs <- synTyConDefn_maybe tc
  , arg_tys `saturates` tyConArity tc
  = Just $! (expand_syn rhs arg_tys)
  | otherwise
  = Nothing

saturates :: [Type p] -> Arity -> Bool
saturates _ 0 = True
saturates [] _ = False
saturates (_:tys) n = assert (n >= 0) $ saturates tys (n-1)

{-# NOINLINE expand_syn #-}
expand_syn :: (HasPass p p1, HasPass p' p2, SubstP p p') => Type p -> [Type p'] -> Type p'
expand_syn rhs arg_tys
  | null arg_tys = panic "closedType rhs"
  | otherwise = go rhs empty_subst arg_tys
  where
    empty_subst = mkEmptySubst (noDomFVs rhs (varsOfType rhs)) (varsOfTypes arg_tys)

    go (TyLamTy _ _) _ [] = pprPanic "expand_syn" (ppr rhs $$ ppr arg_tys)
    go (BigTyLamTy _ _) _ [] = pprPanic "expand_syn" (ppr rhs $$ ppr arg_tys)
    go ty subst [] = substTy subst ty
    go (TyLamTy tv ty) subst (arg:args) = go ty (extendTvSubst subst tv arg) args
    go (BigTyLamTy kv ty) subst (arg:args)
      | Embed ki <- arg = go ty (extendKvSubst subst kv ki) args
      | otherwise = pprPanic "expand_syn" (ppr rhs $$ ppr arg_tys)
    go ty subst args = mkAppTys (substTy subst ty) args

{- **********************************************************************
*                                                                       *
                        Utils (used in ppr/coreView)
                              (or needed in both Core.Kind and Core.Type)
*                                                                       *
********************************************************************** -}

-- * Types

mkNakedTyConTy :: TyCon p -> Type p
mkNakedTyConTy tycon = TyConApp tycon []

mkAppTys :: Type p -> [Type p] -> Type p
mkAppTys ty1 [] = ty1
mkAppTys (TyConApp tc tys1) tys2 = mkTyConApp tc (tys1 ++ tys2)
mkAppTys ty1 tys2 = foldl' AppTy ty1 tys2

mkTyConApp :: TyCon p -> [Type p] -> Type p
mkTyConApp tycon [] = mkTyConTy tycon
mkTyConApp tycon tys = TyConApp tycon tys

splitForAllForAllTyBinders :: HasPass p pass => Type p -> ([ForAllBinder (TyVar p)], Type p)
splitForAllForAllTyBinders ty = split ty ty []
  where
    split _ (ForAllTy b res) bs = split res res (b : bs)
    split orig_ty ty bs | Just ty' <- coreView ty = split orig_ty ty' bs
    split orig_ty _ bs = (reverse bs, orig_ty)
{-# INLINE splitForAllForAllTyBinders #-}

splitForAllKiCoVars :: HasPass p pass => Type p -> ([KiCoVar p], Type p)
splitForAllKiCoVars ty = split ty ty []
  where
    split _ (ForAllKiCo kcv ty) kcvs = split ty ty (kcv:kcvs)
    split orig_ty ty kcvs | Just ty' <- coreView ty = split orig_ty ty' kcvs
    split orig_ty _ kcvs = (reverse kcvs, orig_ty)
{-# INLINE splitForAllKiCoVars #-}

splitTyLamTyBinders :: HasPass p pass => Type p -> ([TyVar p], Type p)
splitTyLamTyBinders ty = split ty ty []
  where
    split _ (TyLamTy b res) bs = split res res (b : bs)
    split orig_ty ty bs | Just ty' <- coreView ty = split orig_ty ty' bs
    split orig_ty _ bs = (reverse bs, orig_ty)
{-# INLINE splitTyLamTyBinders #-}

splitBigLamTyBinders :: HasPass p pass => Type p -> ([KiVar p], Type p)
splitBigLamTyBinders ty = split ty ty []
  where
    split _ (BigTyLamTy b res) bs = split res res (b : bs)
    split orig_ty ty bs | Just ty' <- coreView ty = split orig_ty ty' bs
    split orig_ty _ bs = (reverse bs, orig_ty)
{-# INLINE splitBigLamTyBinders #-}

isForgetfulTy :: HasPass p pass => Type p -> Bool
isForgetfulTy (TyVarTy _) = False
isForgetfulTy (TyConApp tc tys) = isForgetfulSynTyCon tc || any isForgetfulTy tys
isForgetfulTy (AppTy a b) = isForgetfulTy a || isForgetfulTy b
isForgetfulTy (FunTy _ a b) = isForgetfulTy a || isForgetfulTy b
isForgetfulTy (ForAllTy (Bndr tv _) ty)
  = (not $ tv `elemVarSet` (fstOf3 $ varsOfType ty)) || isForgetfulTy ty
isForgetfulTy (TyLamTy tv ty) = (not $ tv `elemVarSet` (fstOf3 $ varsOfType ty)) || isForgetfulTy ty
isForgetfulTy other = pprPanic "isForgetfulTy" (ppr other)

-- * Kinds

splitForAllKiVars :: Kind p -> ([KiVar p], MonoKind p)
splitForAllKiVars ki = split ki []
  where
    split (ForAllKi kv ki) kvs = split ki (kv:kvs)
    split (Mono mki) kvs = (reverse kvs, mki)

-- * Coercions

isReflTyCo :: TypeCoercion p -> Bool
isReflTyCo (TyRefl {}) = True
isReflTyCo (GRefl _ kco) = isReflKiCo kco
isReflTyCo (LiftKCo kco) = isReflKiCo kco
isReflTyCo _ = False

isReflKiCo :: KindCoercion p -> Bool
isReflKiCo (Refl{}) = True
isReflKiCo _ = False

mkReflTyCo :: Type p -> TypeCoercion p
mkReflTyCo (Embed ki) = LiftKCo (mkReflKiCo ki)
mkReflTyCo ty = TyRefl ty

mkReflKiCo :: MonoKind kv -> KindCoercion kv
mkReflKiCo ki = Refl ki

isReflTyCo_maybe :: HasPass p pass => TypeCoercion p -> Maybe (Type p)
isReflTyCo_maybe (TyRefl ty) = Just ty
isReflTyCo_maybe (GRefl ty kco)
  | isReflKiCo kco = pprPanic "isReflTyCo_maybe/GRefl" (ppr ty <+> text "|>" <+> ppr kco)
isReflTyCo_maybe (LiftKCo kco)
  | Just ki <- isReflKiCo_maybe kco
  = Just (Embed ki)
isReflTyCo_maybe _ = Nothing

isReflKiCo_maybe :: KindCoercion p -> Maybe (MonoKind p)
isReflKiCo_maybe (Refl ki) = Just ki
isReflKiCo_maybe _ = Nothing

{- **********************************************************************
*                                                                       *
                        Ppr
*                                                                       *
********************************************************************** -}

-- * Types

pprType :: HasPass p pass => Type p -> SDoc
pprType = pprPrecType topPrec

pprParendType :: HasPass p pass => Type p -> SDoc
pprParendType = pprPrecType appPrec

pprPrecType :: HasPass p pass => PprPrec -> Type p -> SDoc
pprPrecType = pprPrecTypeX emptyTidyEnv

pprPrecTypeX :: HasPass p pass => TidyEnv p -> PprPrec -> Type p -> SDoc
pprPrecTypeX env prec ty
  = getPprStyle $ \ sty ->
    getPprDebug $ \ debug ->
                    if debug
                    then debug_ppr_ty prec ty
                    else panic "pprPrecIfaceType prec (tidyToIfaceTypeStyX env ty sty)"

pprSigmaType :: HasPass p pass => Type p -> SDoc
pprSigmaType ty = text "pprSigmaType not implemented" <+> pprType ty

pprTyVars :: HasPass p pass => [TyVar p] -> SDoc
pprTyVars tvs = sep (map pprTyVar tvs)
 
pprTcTyVars :: [TcTyVar] -> SDoc
pprTcTyVars = pprTyVars . fmap TcTyVar

pprTyVar :: HasPass p pass => TyVar p -> SDoc
pprTyVar tv = parens (ppr tv <+> colon <+> ppr kind)
  where
    kind = varKind tv

debugPprType :: HasPass p pass => Type p -> SDoc
debugPprType ty = debug_ppr_ty topPrec ty

debug_ppr_ty :: HasPass p pass => PprPrec -> Type p -> SDoc

debug_ppr_ty _ (TyVarTy tv) = ppr tv

debug_ppr_ty prec (FunTy { ft_kind = kind, ft_arg = arg, ft_res = res })
  = maybeParen prec funPrec
    $ sep [ debug_ppr_ty funPrec arg
          , char '-' <> ppr kind <> char '>' <+> debug_ppr_ty prec res ]

debug_ppr_ty prec (TyConApp tc tys)
  | null tys = ppr tc
  | otherwise = maybeParen prec appPrec
                $ hang (ppr tc) 2 (sep (map (debug_ppr_ty appPrec) tys))

debug_ppr_ty _ (AppTy t1 t2) = hang (debug_ppr_ty appPrec t1) 2 (debug_ppr_ty appPrec t2)

debug_ppr_ty prec (CastTy ty co)
  = maybeParen prec topPrec
    $ hang (debug_ppr_ty topPrec ty) 2 (text "|>" <+> ppr co)

debug_ppr_ty prec t
  | (bndrs, body) <- splitForAllForAllTyBinders t
  , not (null bndrs)
  = maybeParen prec funPrec
    $ sep [ forAllLit <+> fsep (map ppr_bndr bndrs) <> dot
          , ppr body ]
  where
    ppr_bndr (Bndr tv Specified) = braces (ppr tv)
    ppr_bndr (Bndr tv Inferred) = braces (ppr tv)
    ppr_bndr (Bndr tv Required) = ppr tv

debug_ppr_ty _ ForAllTy{} = panic "debug_ppr_ty ForAllTy"

debug_ppr_ty prec t
  | (bndrs, body) <- splitForAllKiCoVars t
  , not (null bndrs)
  = maybeParen prec funPrec
    $ sep [ forAllLit <+> (braces $ fsep (map ppr bndrs)) <> dot
          , ppr body ]

debug_ppr_ty _ ForAllKiCo{} = panic "debug_ppr_ty ForAllKiCo"

debug_ppr_ty prec t
  | (bndrs, body) <- splitTyLamTyBinders t
  , not (null bndrs)
  = maybeParen prec funPrec
    $ sep [ lambda <+> fsep (map ppr_bndr bndrs) <> arrow
          , ppr body ]
  where
    ppr_bndr tv = parens (ppr tv)

debug_ppr_ty _ TyLamTy{} = panic "debug_ppr_ty TyLamTy"

debug_ppr_ty prec t
  | (bndrs, body) <- splitBigLamTyBinders t
  , not (null bndrs)
  = maybeParen prec funPrec
    $ sep [ biglambda <+> fsep (map ppr_bndr bndrs) <> arrow
          , ppr body ]
  where
    ppr_bndr kv = parens (ppr kv)

debug_ppr_ty _ BigTyLamTy{} = panic "debug_ppr_ty BigTyLamTy"

debug_ppr_ty _ (Embed ki) = ppr ki

debug_ppr_ty _ (KindCoercion co) = text "[KiCo]" <+> (ppr co)

debug_ppr_ty _ (LocalTyRow nm _) = ppr nm

debug_ppr_ty _ (SetRowsTy base rows)
  = ppr base <+> dot <> braces
    (fsep (punctuate comma (map debug_ppr_set_row rows)))

debug_ppr_set_row :: HasPass p pass => SetRow p -> SDoc
debug_ppr_set_row (SetRowVal nm) = ppr nm <+> equals
debug_ppr_set_row (SetRowTy nm ty) = ppr nm <+> equals <+> ppr ty

-- * Kinds

pprKind :: HasPass p pass => Kind p -> SDoc
pprKind = pprPrecKind topPrec

pprMonoKind :: HasPass p pass => MonoKind p -> SDoc
pprMonoKind = pprPrecMonoKind topPrec

pprParendMonoKind :: HasPass p pass => MonoKind p -> SDoc
pprParendMonoKind = pprPrecMonoKind appPrec

pprPrecKind :: HasPass p pass => PprPrec -> Kind p -> SDoc
pprPrecKind = pprPrecKindX emptyTidyEnv

pprPrecMonoKind :: HasPass p pass => PprPrec -> MonoKind p -> SDoc
pprPrecMonoKind = pprPrecMonoKindX emptyTidyEnv

pprPrecKindX :: HasPass p pass => TidyEnv p -> PprPrec -> Kind p -> SDoc
pprPrecKindX env prec ki
  = getPprStyle $ \sty ->
    getPprDebug $ \debug ->
    if debug
    then debug_ppr_ki prec ki
    else text "{pprKind not implemented}"--pprPrecIfaceKind prec (tidyToIfaceKindStyX env ty sty)

pprPrecMonoKindX :: HasPass p pass => TidyEnv p -> PprPrec -> MonoKind p -> SDoc
pprPrecMonoKindX env prec ki
  = getPprStyle $ \sty ->
    getPprDebug $ \debug ->
    if debug
    then debug_ppr_mono_ki prec ki
    else text "{pprKind not implemented}"--pprPrecIfaceKind prec (tidyToIfaceKindStyX env ty sty)

pprRowSig :: HasPass p pass => RowSig p -> SDoc
pprRowSig = pprPrecRowSig topPrec

pprPrecRowSig :: HasPass p pass => PprPrec -> RowSig p -> SDoc
pprPrecRowSig = pprPrecRowSigX emptyTidyEnv

pprPrecRowSigX :: HasPass p pass => TidyEnv p -> PprPrec -> RowSig p -> SDoc
pprPrecRowSigX env prec ki
  = getPprStyle $ \sty ->
    getPprDebug $ \debug ->
    if debug
    then debug_ppr_row ki
    else text "{pprRowSig not implemented}"--pprPrecIfaceKind prec (tidyToIfaceKindStyX env ty sty)

pprKiCo :: HasPass p pass => KindCoercion p -> SDoc
pprKiCo = pprPrecKiCo topPrec

pprPrecKiCo :: HasPass p pass => PprPrec -> KindCoercion p -> SDoc
pprPrecKiCo = pprPrecKiCoX emptyTidyEnv

pprPrecKiCoX
  :: HasPass p pass
  => TidyEnv p
  -> PprPrec
  -> KindCoercion p
  -> SDoc
pprPrecKiCoX _ prec co = getPprStyle $ \sty ->
                       getPprDebug $ \debug ->
                       if debug
                       then debug_ppr_ki_co prec co
                       else panic "pprPrecKiCoX"

debugPprKind :: HasPass p pass => Kind p -> SDoc
debugPprKind ki = debug_ppr_ki topPrec ki

debugPprMonoKind :: HasPass p pass => MonoKind p -> SDoc
debugPprMonoKind ki = debug_ppr_mono_ki topPrec ki

debug_ppr_ki :: HasPass p pass => PprPrec -> Kind p -> SDoc
debug_ppr_ki prec (Mono ki) = debug_ppr_mono_ki prec ki
debug_ppr_ki prec ki
  | (bndrs, body) <- splitForAllKiVars ki
  , not (null bndrs)
  = maybeParen prec funPrec $ sep [ text "forall" <+> fsep (map (braces . ppr) bndrs) <> dot
                                  , ppr body ]
debug_ppr_ki _ _ = panic "debug_ppr_ki unreachable"

debug_ppr_mono_ki :: HasPass p pass => PprPrec -> MonoKind p -> SDoc
debug_ppr_mono_ki _ (KiVarKi kv) = ppr kv
debug_ppr_mono_ki _ (BIKi ki) = ppr ki
debug_ppr_mono_ki _ (KiConApp kc)
  = debug_ppr_kicon kc
debug_ppr_mono_ki prec ki@(KiPredApp pred k1 k2)
  = maybeParen prec appPrec
    $ debug_ppr_mono_ki appPrec k1 <+> ppr pred <+> debug_ppr_mono_ki appPrec k2
debug_ppr_mono_ki prec (FunKi { fk_f = f, fk_arg = arg, fk_res = res })
  = maybeParen prec funPrec
    $ sep [ debug_ppr_mono_ki funPrec arg, fun_arrow <+> debug_ppr_mono_ki prec res]
  where
    fun_arrow = case f of
                  FKF_C_K -> darrow
                  FKF_K_K -> arrow

debug_ppr_kicon :: HasPass p pass => KiCon p -> SDoc
debug_ppr_kicon KiCon{..}
  | Just name <- kicon_name
  = ppr name <> angleBrackets (debug_ppr_kicon KiCon { kicon_name = Nothing, .. })
  | otherwise
  = debug_ppr_mono_ki appPrec kicon_base <+>
    dot <> (braces (fsep (punctuate comma (map debug_ppr_row kicon_rows))))

debug_ppr_row :: HasPass p pass => RowSig p -> SDoc
debug_ppr_row (RowTySig name ty) = ppr name <+> colon <+> debugPprType ty
debug_ppr_row (RowKiSig name ki) = text "type" <+> ppr name <+> colon <+> debugPprMonoKind ki

debug_ppr_ki_co :: HasPass p pass => PprPrec -> KindCoercion p -> SDoc
debug_ppr_ki_co _ (Refl ki) = angleBrackets (ppr ki)
debug_ppr_ki_co _ BI_U_A = angleBrackets (text "UKd < AKd")
debug_ppr_ki_co _ BI_A_L = angleBrackets (text "AKd < LKd")
debug_ppr_ki_co _ (BI_U_LTEQ ki) = angleBrackets (text "UKd < " <> ppr ki)
debug_ppr_ki_co _ (BI_LTEQ_L ki) = angleBrackets (ppr ki <> text " < LKd")
debug_ppr_ki_co _ (LiftEq ki) = angleBrackets (text "LiftEq" <+> ppr ki)
debug_ppr_ki_co _ (LiftLT ki) = angleBrackets (text "LiftLT" <+> ppr ki)
debug_ppr_ki_co prec (FunCo _ _ co1 co2)
  = maybeParen prec funPrec
    $ sep (debug_ppr_ki_co funPrec co1 : ppr_fun_tail co2)
  where
    ppr_fun_tail (FunCo _ _ co1 co2)
      = (arrow <+> debug_ppr_ki_co funPrec co1)
        : ppr_fun_tail co2
    ppr_fun_tail other = [ arrow <+> ppr other ]
debug_ppr_ki_co prec (SymCo co) = maybeParen prec appPrec $ sep [ text "Sym"
                                                                , nest 4 (ppr co) ]
debug_ppr_ki_co prec (TransCo co1 co2)
  = let ppr_trans (TransCo c1 c2) = semi <+> debug_ppr_ki_co topPrec c1 : ppr_trans c2
        ppr_trans c = [semi <+> debug_ppr_ki_co opPrec c]
  in maybeParen prec opPrec
     $ vcat (debug_ppr_ki_co topPrec co1 : ppr_trans co2)
debug_ppr_ki_co _ (HoleCo co) = ppr co
debug_ppr_ki_co _ (KiCoVarCo cv) = ppr cv
debug_ppr_ki_co _ (KiRowCo base rows)
  = angleBrackets $
    debug_ppr_ki_co topPrec base
    <+> dot <> braces
    (fsep (punctuate comma (map debug_ppr_row_co rows)))
debug_ppr_ki_co _ _ = panic "debug_ppr_ki_co"

debug_ppr_row_co :: HasPass p pass => RowCoercion p -> SDoc
debug_ppr_row_co (RowTySigCo nm co) = ppr nm <+> equals <+> ppr co
debug_ppr_row_co (RowKiSigCo nm co) = ppr nm <+> equals <+> ppr co
