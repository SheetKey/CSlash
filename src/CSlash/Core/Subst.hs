{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Subst where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import {-# SOURCE #-} CSlash.Core ( CoreExpr )
import {-# SOURCE #-} CSlash.Core.Ppr ()
import {-# SOURCE #-} CSlash.Core.Type ( mkAppTy, mkTyConApp, mkCastTy )
import {-# SOURCE #-} CSlash.Core.Type.Ppr ( pprTyVar )

import CSlash.Core.TyCon
import CSlash.Core.Type.Rep
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs
import CSlash.Core.Type.FVs

import CSlash.Types.Var.TyVar
import CSlash.Types.Var.KiVar
import CSlash.Types.Var.CoVar
import CSlash.Types.Var.Class
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env

import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Misc
import CSlash.Types.Unique
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Set
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Data.Maybe (orElse)

import Data.Kind (Constraint)

{- **********************************************************************
*                                                                       *
                        Simple substs
*                                                                       *
********************************************************************** -}

fromZkType :: HasPass p pass => Type Zk -> Type p
fromZkType ty = let subst = mkEmptySubst (varsOfType ty) (emptyVarSet, emptyVarSet, emptyVarSet)
              in substTy subst ty

fromZkKind :: HasPass p pass => Kind Zk -> Kind p
fromZkKind ki = let subst = mkEmptySubst (emptyVarSet, emptyVarSet, varsOfKind ki)
                                       (emptyVarSet, emptyVarSet, emptyVarSet)
              in substKi subst ki

{- **********************************************************************
*                                                                       *
                        Substitutions
*                                                                       *
********************************************************************** -}

-- type SubstP :: * -> * -> Constraint
-- type family SubstP p p' where
--   SubstP Zk p' = ()
--   SubstP Tc p' = p' ~ Tc

data Subst p p' = Subst
  { tv_in_scope :: InScopeSet (TyVar p')
  , tv_env :: TvSubstEnv p p'

  , kcv_in_scope :: InScopeSet (KiCoVar p')
  , kcv_env :: KCvSubstEnv p p'

  , kv_in_scope :: InScopeSet (KiVar p')
  , kv_env :: KvSubstEnv p p'
  }

type TvSubstEnv p p' = VarEnv (TyVar p) (Type p')
type KCvSubstEnv p p' = VarEnv (KiCoVar p) (KindCoercion p')
type KvSubstEnv p p' = VarEnv (KiVar p) (MonoKind p')

instance IsPass p' => Outputable (Subst p (CsPass p')) where
  ppr Subst {..} = vcat [ text "<<TvInScope =" <+> ppIS tv_in_scope
                        , text "TvSubst =" <+> ppr tv_env <> char '>'
                        , text "<KCvInScope =" <+> ppIS kcv_in_scope
                        , text "KCvSubst =" <+> ppr kcv_env <> char '>'
                        , text "<KvInScope =" <+> ppIS kv_in_scope
                        , text "KvSubst =" <+> ppr kv_env <> text ">>" ]
    where
      ppIS :: Outputable a => InScopeSet a -> SDoc
      ppIS is = pprVarSet (getInScopeVars is) (braces . fsep . map ppr)

type SubstInScope p' = ( InScopeSet (TyVar p')
                       , InScopeSet (KiCoVar p')
                       , InScopeSet (KiVar p') )

mkInScopeSets :: (TyVarSet p, KiCoVarSet p, KiVarSet p) -> SubstInScope p
mkInScopeSets (tv, kcv, kv) = (mkInScopeSet tv, mkInScopeSet kcv, mkInScopeSet kv)

emptySubst :: Subst p p'
emptySubst = Subst { tv_in_scope = emptyInScopeSet
                   , tv_env = emptyVarEnv
                   , kcv_in_scope = emptyInScopeSet
                   , kcv_env = emptyVarEnv
                   , kv_in_scope = emptyInScopeSet
                   , kv_env = emptyVarEnv }

-- Takes the free vars in the domain and range.
-- Uses range fvs as initial in scope set.
-- Treats domain free vars as a var binder.
-- Returns: subst from dom vars to self (with type change)
--          in-scope set containing range fvs and type-changed dom fvs
-- Used when we have Subst Zk Tc (e.g. for instantiating builtins during type checking)
mkEmptySubst
  :: (HasPass p' pass, SubstP p p')
  => (TyVarSet p, KiCoVarSet p, KiVarSet p)    -- domain FVs
  -> (TyVarSet p', KiCoVarSet p', KiVarSet p') -- range FVs
  -> Subst p p'
mkEmptySubst (dom_tvs, dom_kcvs, dom_kvs) rng_fvs
  = let (tv_is, kcv_is, kv_is) = mkInScopeSets rng_fvs
        subst1 = Subst { tv_in_scope = tv_is, tv_env = emptyVarEnv
                       , kcv_in_scope = kcv_is, kcv_env = emptyVarEnv
                       , kv_in_scope = kv_is, kv_env = emptyVarEnv }
        subst2 = nonDetStrictFoldVarSet (\kv subst -> bindFreeDomKv subst kv)
                 subst1 dom_kvs
        subst3 = nonDetStrictFoldVarSet (\kcv subst -> bindFreeDomKCv subst kcv)
                 subst2 dom_kcvs
        subst4 = nonDetStrictFoldVarSet (\tv subst -> bindFreeDomTv subst tv)
                 subst3 dom_tvs
  in subst4

bindFreeDomKv :: SubstP p p' => Subst p p' -> KiVar p -> Subst p p'
bindFreeDomKv subst@(Subst {..}) dom_var
  = case lookupInScope_Directly kv_in_scope (varUnique dom_var) of
      Just range_var -> Subst { kv_env = extendVarEnv kv_env dom_var (mkKiVarKi range_var), .. }
      Nothing -> let range_var = vacuous_kv dom_var
                 in Subst { kv_in_scope = kv_in_scope `extendInScopeSet` range_var
                          , kv_env = extendVarEnv kv_env dom_var (mkKiVarKi range_var)
                          , .. }

bindFreeDomKCv :: (HasPass p' pass, SubstP p p') => Subst p p' -> KiCoVar p -> Subst p p'
bindFreeDomKCv subst@(Subst {..}) dom_var
  = case lookupInScope_Directly kcv_in_scope (varUnique dom_var) of
      Just range_var -> Subst { kcv_env = extendVarEnv kcv_env dom_var (mkKiCoVarCo range_var)
                              , .. }
      Nothing -> let range_var = vacuous_set_kcv_kind
                                 (substMonoKi subst (varKind dom_var)) dom_var
                 in Subst { kcv_in_scope = kcv_in_scope `extendInScopeSet` range_var
                          , kcv_env = extendVarEnv kcv_env dom_var (mkKiCoVarCo range_var)
                          , .. }

bindFreeDomTv :: (HasPass p' pass, SubstP p p') => Subst p p' -> TyVar p -> Subst p p'
bindFreeDomTv subst@(Subst {..}) dom_var
  = case lookupInScope_Directly tv_in_scope (varUnique dom_var) of
      Just range_var -> Subst { tv_env = extendVarEnv tv_env dom_var (mkTyVarTy range_var), .. }
      Nothing -> let range_var = vacuous_set_tv_kind
                                 (substMonoKi subst (varKind dom_var)) dom_var
                 in Subst { tv_in_scope = tv_in_scope `extendInScopeSet` range_var
                          , tv_env = extendVarEnv tv_env dom_var (mkTyVarTy range_var)
                          , .. }

noDomFVs
  :: Outputable thing => thing
  -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
  -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
noDomFVs thing (tv, kcv, kv) =
  assertPpr (isEmptyVarSet tv && isEmptyVarSet kcv && isEmptyVarSet kv)
  (vcat [ text "noDomFVs" <+> ppr thing
        , text "tvs" <+> ppr tv
        , text "kcvs" <+> ppr kcv
        , text "kvs" <+> ppr kv ])
  (emptyVarSet, emptyVarSet, emptyVarSet)

-- mkEmptyKvSubst :: InScopeSet (KiVar p') -> Subst p p'
-- mkEmptyKvSubst kv_is = emptySubst { kv_in_scope = kv_is }

mkKvSubst :: InScopeSet (KiVar p') -> KvSubstEnv p p' -> Subst p p'
mkKvSubst kv_is kenv = emptySubst { kv_in_scope = kv_is, kv_env = kenv }

isEmptySubst :: Subst p p' -> Bool
isEmptySubst Subst { tv_env = tv_env, kcv_env = kcv_env, kv_env = kv_env }
  = isEmptyVarEnv tv_env
    && isEmptyVarEnv kcv_env
    && isEmptyVarEnv kv_env

isEmptySubstTy :: Subst p p' -> Bool
isEmptySubstTy Subst { tv_env = tv_env, kcv_env = kcv_env, kv_env = kv_env }
  = isEmptyVarEnv tv_env
    && isEmptyVarEnv kcv_env
    && isEmptyVarEnv kv_env

isEmptySubstKi :: Subst p p' -> Bool
isEmptySubstKi Subst { kv_env = kv_env }
  = isEmptyVarEnv kv_env

extendTvSubstInScopeSet :: Subst p p' -> TyVarSet p' -> Subst p p'
extendTvSubstInScopeSet (Subst { tv_in_scope = is, .. }) vs
  = Subst { tv_in_scope = is `extendInScopeSetSet` vs, .. }

extendKCvSubstInScopeSet :: Subst p p' -> KiCoVarSet p' -> Subst p p'
extendKCvSubstInScopeSet (Subst { kcv_in_scope = is, .. }) vs
  = Subst { kcv_in_scope = is `extendInScopeSetSet` vs, .. }

extendKvSubstInScopeSet :: Subst p p' -> KiVarSet p' -> Subst p p'
extendKvSubstInScopeSet (Subst { kv_in_scope = is, .. }) vs
  = Subst { kv_in_scope = is `extendInScopeSetSet` vs, .. }

extendSubstInScopeSetsSets :: Subst p p' -> (TyVarSet p', KiCoVarSet p', KiVarSet p') -> Subst p p'
extendSubstInScopeSetsSets (Subst { tv_in_scope = tis
                             , kcv_in_scope = kcis
                             , kv_in_scope = kis
                             , .. })
                      (ntis, nkcis, nkis) 
  = Subst { tv_in_scope = tis `extendInScopeSetSet` ntis
          , kcv_in_scope = kcis `extendInScopeSetSet` nkcis
          , kv_in_scope = kis `extendInScopeSetSet` nkis
          , .. }

extendTvSubstAndInScope :: HasPass p' pass => Subst p p' -> TyVar p -> Type p' -> Subst p p'
extendTvSubstAndInScope (Subst { tv_env = tenv, .. }) tv ty
  = extendSubstInScopeSetsSets (Subst { tv_env = extendVarEnv tenv tv ty, .. }) (varsOfType ty)

extendTvSubst :: Subst p p' -> TyVar p -> Type p' -> Subst p p'
extendTvSubst (Subst { tv_env = tvs, ..}) tv ty
  = Subst { tv_env =  extendVarEnv tvs tv ty, .. }

extendKCvSubst :: Subst p p' -> KiCoVar p -> KindCoercion p' -> Subst p p'
extendKCvSubst (Subst { kcv_env = kcvs, ..}) kcv kco
  = Subst { kcv_env = extendVarEnv kcvs kcv kco, .. }

extendKvSubst :: Subst p p' -> KiVar p -> MonoKind p' -> Subst p p'
extendKvSubst (Subst { kv_env = kvs, ..}) kv ki
  = Subst { kv_env = extendVarEnv kvs kv ki, .. }

extendTvSubstWithClone :: Subst p p' -> TyVar p -> TyVar p' -> Subst p p'
extendTvSubstWithClone (Subst { tv_in_scope = tis, tv_env = tvs, .. }) tv tv'
  = Subst { tv_in_scope = tis `extendInScopeSet` tv'
          , tv_env = extendVarEnv tvs tv (mkTyVarTy tv')
          , .. }

extendKCvSubstWithClone :: Subst p p' -> KiCoVar p -> KiCoVar p' -> Subst p p'
extendKCvSubstWithClone (Subst { kcv_in_scope = kcis, kcv_env = kcvs, .. }) kcv kcv'
  = Subst { kcv_in_scope = kcis `extendInScopeSet` kcv'
          , kcv_env = extendVarEnv kcvs kcv (mkKiCoVarCo kcv')
          , .. }

extendKCvSubstWithHole :: Subst p Tc -> KiCoVar p -> KindCoercionHole -> Subst p Tc
extendKCvSubstWithHole (Subst { kcv_in_scope = kcis, kcv_env = kcvs, .. }) kcv hole
  = Subst { kcv_in_scope = kcis `extendInScopeSet` TcCoVar (coHoleCoVar hole)
          , kcv_env = extendVarEnv kcvs kcv (HoleCo hole)
          , .. }

extendKvSubstWithClone :: Subst p p' -> KiVar p -> KiVar p' -> Subst p p'
extendKvSubstWithClone (Subst { kv_in_scope = kis, kv_env = kvs, .. }) kv kv'
  = Subst { kv_in_scope = kis `extendInScopeSet` kv'
          , kv_env = extendVarEnv kvs kv (mkKiVarKi kv')
          , .. }

zapSubst :: Subst p p' -> Subst p p'
zapSubst Subst {..} = Subst { tv_env = emptyVarEnv
                            , kcv_env = emptyVarEnv
                            , kv_env = emptyVarEnv
                            , ..
                            }


{- **********************************************************************
*                                                                       *
                Validity Check
*                                                                       *
********************************************************************** -}

isValidSubst :: HasPass p' pass => Subst p p' -> Bool
isValidSubst Subst {..} =
  (tenvFVs1 `varSetInScope` tv_in_scope) &&
  (tenvFVs2 `varSetInScope` kcv_in_scope) &&
  (tenvFVs3 `varSetInScope` kv_in_scope) &&
  (kcenvFVs1 `varSetInScope` kcv_in_scope) &&
  (kcenvFVs2 `varSetInScope` kv_in_scope) &&
  (kenvFVs `varSetInScope` kv_in_scope)
  where
    (tenvFVs1, tenvFVs2, tenvFVs3) = varsOfTyVarEnv tv_env
    (kcenvFVs1, kcenvFVs2) = varsOfKiCoVarEnv kcv_env
    kenvFVs = varsOfMonoKiVarEnv kv_env

checkValidSubst
  :: (HasDebugCallStack, HasPass p' pass)
  => Subst p p' --  -> [Type p] -> [KindCoercion p] -> [Kind p]
  -> a -> a
checkValidSubst subst@(Subst {..}) a
  = assertPpr (isValidSubst subst)
    (vcat [ text "tv_in_scope" <+> ppr tv_in_scope
          , text "tenv" <+> ppr tv_env
          , text "tenvFVs" <+> ppr (varsOfTyVarEnv tv_env)
          , text "kcv_in_scope" <+> ppr kcv_in_scope
          , text "kcenv" <+> ppr kcv_env
          , text "kcenvFVs" <+> ppr (varsOfKiCoVarEnv kcv_env)
          , text "kv_in_scope" <+> ppr kv_in_scope
          , text "kenv" <+> ppr kv_env
          , text "kenvFVs" <+> ppr (varsOfMonoKiVarEnv kv_env)
          ]) $
    -- assertPpr fvsInScope
    -- (vcat [ text "tv_in_scope" <+> ppr tv_in_scope
    --       , text "tenv" <+> ppr tv_env
    --       , text "tenvFVs" <+> ppr (shallowVarsOfTyVarEnv tv_env)
    --       , text "kcv_in_scope" <+> ppr kcv_in_scope
    --       , text "kcenv" <+> ppr kcv_env
    --       , text "kcenvFVs" <+> ppr (shallowVarsOfKiCoVarEnv kcv_env)
    --       , text "kv_in_scope" <+> ppr kv_in_scope
    --       , text "kenv" <+> ppr kv_env
    --       , text "kenvFVs" <+> ppr (varsOfMonoKiVarEnv kv_env)
    --       ])
    a
  -- where
  --   (tvs1, kcvs1, kvs1) = shallowVarsOfTypes tys
    

{- **********************************************************************
*                                                                       *
                Performing kind substitutions
*                                                                       *
********************************************************************** -}

substKi :: (HasDebugCallStack, HasPass p' pass, SubstP p p') => Subst p p' -> Kind p -> Kind p'
substKi subst ki = checkValidSubst subst $
                   subst_ki subst ki


substMonoKi
  :: (HasDebugCallStack, HasPass p' pass, SubstP p p')
  => Subst p p' -> MonoKind p -> MonoKind p'
substMonoKi subst ki = checkValidSubst subst $
                       subst_mono_ki subst ki

substMonoKis
  :: (HasDebugCallStack, HasPass p' pass, SubstP p p')
  => Subst p p' -> [MonoKind p] -> [MonoKind p']
substMonoKis subst kis = checkValidSubst subst $
                         map (subst_mono_ki subst) kis

substKiUnchecked :: (HasPass p' pass, SubstP p p') => Subst p p' -> Kind p -> Kind p'
substKiUnchecked subst ki = subst_ki subst ki

substMonoKiUnchecked :: (HasPass p' pass, SubstP p p') => Subst p p' -> MonoKind p -> MonoKind p'
substMonoKiUnchecked subst ki = subst_mono_ki subst ki

subst_ki :: (HasPass p' pass, SubstP p p') => Subst p p' -> Kind p -> Kind p'
subst_ki subst ki = go ki
  where
    go (Mono ki) = Mono $! subst_mono_ki subst ki
    go (ForAllKi kv ki) = case substKiVarBndr subst kv of
                            (subst', kv') -> (ForAllKi $! kv') $! (subst_ki subst' ki)

subst_mono_ki :: HasPass p' pass => Subst p p' -> MonoKind p -> MonoKind p'
subst_mono_ki subst ki = go ki
  where
    go (KiVarKi kv) = substKiVar subst kv
    go (BIKi k) = BIKi k
    go ki@(FunKi { fk_arg = arg, fk_res = res })
      = let !arg' = go arg
            !res' = go res
        in ki { fk_arg = arg', fk_res = res' }
    go ki@(KiPredApp pred k1 k2)
      = let !k1' = go k1
            !k2' = go k2
      in (mkKiPredApp $! pred) k1' k2'

substKiVar :: HasPass p' pass => Subst p p' -> KiVar p -> MonoKind p'
substKiVar subst@(Subst { kv_env = env }) kv
  = lookupVarEnv env kv `orElse` pprPanic "substKiVar" (ppr kv $$ ppr subst)

substKiVarBndr :: (HasPass p' pass, SubstP p p') => Subst p p' -> KiVar p -> (Subst p p', KiVar p')
substKiVarBndr subst@(Subst {..}) old_var
  = assertPpr no_capture (ppr old_var $$ ppr new_var $$ ppr subst) $
    ( Subst { kv_in_scope = kv_in_scope `extendInScopeSet` new_var
           , kv_env = new_env, .. }
    , new_var)
  where
    no_capture = not (new_var `elemVarSet` varsOfMonoKiVarEnv kv_env)

    new_var = uniqAway kv_in_scope (vacuous_kv old_var)

    new_env = extendVarEnv kv_env old_var (mkKiVarKi new_var)

class SubstP p p' where
  vacuous_kv :: KiVar p -> KiVar p'

  vacuous_set_tv_kind :: MonoKind p' -> TyVar p -> TyVar p'
  vacuous_set_kcv_kind :: MonoKind p' -> KiCoVar p -> KiCoVar p'

  vacuous_tycon :: TyCon p -> TyCon p'

instance {-# INCOHERENT #-} SubstP Zk p where
  vacuous_kv KiVar {..} = KiVar {..}

  vacuous_set_tv_kind ki (TyVar {..}) = TyVar { tv_kind = ki, .. }
  vacuous_set_kcv_kind ki (CoVar {..}) = CoVar { cv_thing = ki, .. }

  vacuous_tycon = fromZkTyCon

instance {-# INCOHERENT #-} SubstP p Tc where
  vacuous_kv kv = case kv of
    KiVar {..} -> KiVar {..}
    TcKiVar tckv -> TcKiVar tckv

  vacuous_set_tv_kind ki tv = case tv of
    TyVar {..} -> TyVar { tv_kind = ki, ..}
    TcTyVar tckv -> TcTyVar tckv { tc_tv_kind = ki }

  vacuous_set_kcv_kind ki kcv = case kcv of
    CoVar {..} -> CoVar { cv_thing = ki, .. }
    TcCoVar v -> TcCoVar $ v { tc_cv_thing = ki }

  vacuous_tycon = toTcTyCon

instance SubstP p p where
  vacuous_kv kv = kv

  vacuous_set_tv_kind ki tv = case tv of
    TyVar {..} -> TyVar { tv_kind = ki, ..}
    TcTyVar tckv -> TcTyVar tckv { tc_tv_kind = ki }

  vacuous_set_kcv_kind ki kcv = case kcv of
    CoVar {..} -> CoVar { cv_thing = ki, .. }
    TcCoVar v -> TcCoVar $ v { tc_cv_thing = ki }

  vacuous_tycon tc = tc

subst_kco :: HasPass p' pass => Subst p p' -> KindCoercion p -> KindCoercion p'
subst_kco subst co = go co
  where
    go_mki = subst_mono_ki subst

    go (Refl ki) = mkReflKiCo $! go_mki ki
    go BI_U_A = BI_U_A
    go BI_A_L = BI_A_L
    go (BI_U_LTEQ ki) = BI_U_LTEQ $! go_mki ki
    go (BI_LTEQ_L ki) = BI_LTEQ_L $! go_mki ki
    go (LiftEq co) = LiftEq $! go co
    go (LiftLT co) = LiftLT $! go co
    go (FunCo f1 f2 c1 c2) = (mkFunKiCo2 f1 f2 $! go c1) $! go c2
    go (KiCoVarCo kcv) = substKiCoVar subst kcv
    go (SymCo co) = mkSymKiCo $! go co
    go (TransCo c1 c2) = (mkTransKiCo $! go c1) $! go c2
    go (SelCo d co) = mkSelCo d $! go co
    go (HoleCo h) = panic "HoleCo $! go_hole h"

    go_hole h@(KindCoercionHole { kch_co_var = cv })
      = panic "h { kch_co_var = updateVarKind go_mki cv }"

substKiCoVar :: Subst p p' -> KiCoVar p -> KindCoercion p'
substKiCoVar (Subst { kcv_env = env }) kcv
  = lookupVarEnv env kcv `orElse` pprPanic "substKiCoVar" (ppr kcv $$ ppr env)

{- **********************************************************************
*                                                                       *
                Performing type substitutions
*                                                                       *
********************************************************************** -}

substTy :: (HasDebugCallStack, HasPass p' pass, SubstP p p') => Subst p p' -> Type p -> Type p'
substTy subst ty = checkValidSubst subst $
                   subst_ty subst ty

substTyUnchecked :: (HasPass p' pass, SubstP p p') => Subst p p' -> Type p -> Type p'
substTyUnchecked subst ty = subst_ty subst ty

subst_ty :: (HasPass p' pass, SubstP p p') => Subst p p' -> Type p -> Type p'
subst_ty subst ty = go ty
  where
    go (TyVarTy tv) = substTyVar subst tv
    go (AppTy fun arg) = (mkAppTy $! (go fun)) $! (go arg)
    go (TyLamTy tv ty)
      = case substTyVarBndr subst tv of
          (subst', tv') -> (TyLamTy $! tv') $! (subst_ty subst' ty)
    go (BigTyLamTy kv ty)
      = case substKiVarBndr subst kv of
          (subst', kv') -> (BigTyLamTy $! kv') $! (subst_ty subst' ty)
    go (TyConApp tc []) = (mkTyConTy $! vacuous_tycon tc)
    go (TyConApp tc tys) = (mkTyConApp $! vacuous_tycon tc) $! strictMap go tys
    go ty@(FunTy { ft_kind = kind, ft_arg = arg, ft_res = res })
      = let !kind' = substMonoKi subst kind
            !arg' = go arg
            !res' = go res
        in ty { ft_kind = kind', ft_arg = arg', ft_res = res' }
    go (ForAllTy (Bndr tv vis) ty)
      = case substTyVarBndr subst tv of
          (subst', tv') -> (ForAllTy $! ((Bndr $! tv') vis))
                                     $! (subst_ty subst' ty)
    go (ForAllKiCo kcv ty)
      = case substKiCoVarBndr subst kcv of
          (subst', kcv') -> (ForAllKiCo $! kcv') $! (subst_ty subst' ty)
    go (Embed mki) = Embed $! substMonoKi subst mki
    go (CastTy ty kco) = (mkCastTy $! (go ty)) $! subst_kco subst kco
    go co@(KindCoercion kco) = KindCoercion $! subst_kco subst kco

substTyVar :: HasPass p' pass => Subst p p' -> TyVar p -> Type p'
substTyVar (Subst { tv_env = tenv }) tv
  = lookupVarEnv tenv tv `orElse` pprPanic "substTyVar" (ppr tv $$ ppr tenv)

substTyVarBndr
  :: (HasDebugCallStack, HasPass p' pass, SubstP p p')
  => Subst p p' -> TyVar p -> (Subst p p', TyVar p')
substTyVarBndr = substTyVarBndrUsing substMonoKi

substTyVarBndrUsing
  :: (HasPass p' pass, SubstP p p')
  => (Subst p p' -> MonoKind p -> MonoKind p')
  -> Subst p p' -> TyVar p -> (Subst p p', TyVar p')
substTyVarBndrUsing subst_fn subst@(Subst {..}) old_var
  = assertPpr no_capture (pprTyVar old_var $$ pprTyVar new_var $$ ppr subst) $
    (Subst { tv_in_scope = tv_in_scope `extendInScopeSet` new_var
           , tv_env = new_env
           , .. }
    , new_var )
  where
    no_capture = not (new_var `elemVarSet` fstOf3 (varsOfTyVarEnv tv_env))

    new_var = uniqAway tv_in_scope $
              vacuous_set_tv_kind (subst_fn subst (varKind old_var)) old_var

    new_env = extendVarEnv tv_env old_var (mkTyVarTy new_var)

substKiCoVarBndr
  :: (HasDebugCallStack, HasPass p' pass, SubstP p p')
  => Subst p p' -> KiCoVar p -> (Subst p p', KiCoVar p')
substKiCoVarBndr = substKiCoVarBndrUsing substMonoKi

substKiCoVarBndrUsing
  :: (HasPass p' pass, SubstP p p')
  => (Subst p p' -> MonoKind p -> MonoKind p')
  -> Subst p p' -> KiCoVar p -> (Subst p p', KiCoVar p')
substKiCoVarBndrUsing subst_fn subst@(Subst {..}) old_var
  = assertPpr no_capture (ppr old_var $$ ppr new_var $$ ppr subst) $
    (Subst { kcv_in_scope = kcv_in_scope `extendInScopeSet` new_var
           , kcv_env = new_env
           , .. }
    , new_var )
  where
    no_capture = not (new_var `elemVarSet` fst (varsOfKiCoVarEnv kcv_env))

    new_var = uniqAway kcv_in_scope $
              vacuous_set_kcv_kind (subst_fn subst (varKind old_var)) old_var

    new_env = extendVarEnv kcv_env old_var (mkKiCoVarCo new_var)
