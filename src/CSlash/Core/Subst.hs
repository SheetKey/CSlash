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

import CSlash.Core.Type.Rep
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs
import CSlash.Core.Type.FVs

import CSlash.Types.Var
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

instance Outputable (Subst p p')

type SubstInScope p' = ( InScopeSet (TyVar p')
                       , InScopeSet (KiCoVar p')
                       , InScopeSet (KiVar p') )

mkInScopeSets :: (TyVarSet p, KiCoVarSet p, KiVarSet p) -> SubstInScope p
mkInScopeSets (tv, kcv, kv) = (mkInScopeSet tv, mkInScopeSet kcv, mkInScopeSet kv)

getSubstInScope :: Subst p p' -> SubstInScope p'
getSubstInScope Subst {..} = (tv_in_scope, kcv_in_scope, kv_in_scope)

emptySubst :: Subst p p'
emptySubst = mkEmptySubst (emptyInScopeSet, emptyInScopeSet, emptyInScopeSet)

mkEmptySubst :: SubstInScope p' -> Subst p p'
mkEmptySubst (tv_in_scope, kcv_in_scope, kv_in_scope)
  = Subst { tv_env = emptyVarEnv
          , kcv_env = emptyVarEnv
          , kv_env = emptyVarEnv
          , ..
          }

mkEmptyKvSubst :: InScopeSet (KiVar p') -> Subst p p'
mkEmptyKvSubst kv_is = emptySubst { kv_in_scope = kv_is }

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

extendInScopeSetsSets :: Subst p p' -> (TyVarSet p', KiCoVarSet p', KiVarSet p') -> Subst p p'
extendInScopeSetsSets (Subst { tv_in_scope = tis
                             , kcv_in_scope = kcis
                             , kv_in_scope = kis
                             , .. })
                      (ntis, nkcis, nkis) 
  = Subst { tv_in_scope = tis `extendInScopeSetSet` ntis
          , kcv_in_scope = kcis `extendInScopeSetSet` nkcis
          , kv_in_scope = kis `extendInScopeSetSet` nkis
          , .. }

extendTvSubstAndInScope :: Subst p p' -> TyVar p -> Type p' -> Subst p p'
extendTvSubstAndInScope (Subst { tv_env = tenv, .. }) tv ty
  = extendInScopeSetsSets (Subst { tv_env = extendVarEnv tenv tv ty, .. }) (varsOfType ty)

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

isValidSubst :: Subst p p' -> Bool
isValidSubst Subst {..}
  = panic "isValidSubst"

checkValidSubst
  :: HasDebugCallStack
  => Subst p p'
  -> [Type p] -> [KindCoercion p] -> [Kind p]
  -> a -> a
checkValidSubst = panic "checkValidSubst"

{- **********************************************************************
*                                                                       *
                Performing kind substitutions
*                                                                       *
********************************************************************** -}

substKi :: (HasDebugCallStack, SubstP p p') => Subst p p' -> Kind p -> Kind p'
substKi subst ki = checkValidSubst subst [] [] [ki] $
                   subst_ki subst ki


substMonoKi :: (HasDebugCallStack, SubstP p p') => Subst p p' -> MonoKind p -> MonoKind p'
substMonoKi subst ki = checkValidSubst subst [] [] [Mono ki] $
                       subst_mono_ki subst ki

substMonoKis :: (HasDebugCallStack, SubstP p p') => Subst p p' -> [MonoKind p] -> [MonoKind p']
substMonoKis subst kis = checkValidSubst subst [] [] (Mono <$> kis) $
                         map (subst_mono_ki subst) kis

substKiUnchecked :: SubstP p p' => Subst p p' -> Kind p -> Kind p'
substKiUnchecked subst ki = subst_ki subst ki

substMonoKiUnchecked :: SubstP p p' => Subst p p' -> MonoKind p -> MonoKind p'
substMonoKiUnchecked subst ki = subst_mono_ki subst ki

subst_ki :: SubstP p p' => Subst p p' -> Kind p -> Kind p'
subst_ki subst ki = go ki
  where
    go (Mono ki) = Mono $! subst_mono_ki subst ki
    go (ForAllKi kv ki) = case substKiVarBndr subst kv of
                            (subst', kv') -> (ForAllKi $! kv') $! (subst_ki subst' ki)

subst_mono_ki :: Subst p p' -> MonoKind p -> MonoKind p'
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

substKiVar :: Subst p p' -> KiVar p -> MonoKind p'
substKiVar (Subst { kv_env = env }) kv
  = lookupVarEnv env kv `orElse` pprPanic "substKiVar" (ppr kv $$ ppr env)

substKiVarBndr :: SubstP p p' => Subst p p' -> KiVar p -> (Subst p p', KiVar p')
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

instance {-# INCOHERENT #-} SubstP Zk p where
  vacuous_kv KiVar {..} = KiVar {..}

  vacuous_set_tv_kind ki (TyVar {..}) = TyVar { tv_kind = ki, .. }

instance {-# INCOHERENT #-} SubstP p Tc where
  vacuous_kv kv = case kv of
    KiVar {..} -> KiVar {..}
    TcKiVar tckv -> TcKiVar tckv

  vacuous_set_tv_kind ki tv = case tv of
    TyVar {..} -> TyVar { tv_kind = ki, ..}
    TcTyVar tckv -> TcTyVar tckv { tc_tv_kind = ki }

instance SubstP p p where
  vacuous_kv kv = case kv of
    KiVar {..} -> KiVar {..}
    TcKiVar tckv -> TcKiVar tckv

  vacuous_set_tv_kind ki tv = case tv of
    TyVar {..} -> TyVar { tv_kind = ki, ..}
    TcTyVar tckv -> TcTyVar tckv { tc_tv_kind = ki }

subst_kco :: Subst p p' -> KindCoercion p -> KindCoercion p'
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

substTy :: (HasDebugCallStack, SubstP p p') => Subst p p' -> Type p -> Type p'
substTy subst ty = checkValidSubst subst [ty] [] [] $
                   subst_ty subst ty

substTyUnchecked :: SubstP p p' => Subst p p' -> Type p -> Type p'
substTyUnchecked subst ty = subst_ty subst ty

subst_ty :: SubstP p p' => Subst p p' -> Type p -> Type p'
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
    go ty@(TyConApp tc []) = tc `seq` panic "ty"
    go (TyConApp tc tys) = (mkTyConApp $! panic "tc") $! strictMap go tys
    go ty@(FunTy { ft_kind = kind, ft_arg = arg, ft_res = res })
      = let !kind' = substMonoKi subst kind
            !arg' = go arg
            !res' = go res
        in ty { ft_kind = kind', ft_arg = arg', ft_res = res' }
    go (ForAllTy (Bndr tv vis) ty)
      = case substTyVarBndr subst tv of
          (subst', tv') -> (ForAllTy $! ((Bndr $! tv') vis))
                                     $! (subst_ty subst' ty)
    go (Embed mki) = Embed $! substMonoKi subst mki
    go (CastTy ty kco) = (mkCastTy $! (go ty)) $! subst_kco subst kco
    go co@(KindCoercion kco) = KindCoercion $! subst_kco subst kco

substTyVar :: Subst p p' -> TyVar p -> Type p'
substTyVar (Subst { tv_env = tenv }) tv
  = lookupVarEnv tenv tv `orElse` pprPanic "substTyVar" (ppr tv $$ ppr tenv)

substTyVarBndr
  :: (HasDebugCallStack, SubstP p p')
  => Subst p p' -> TyVar p -> (Subst p p', TyVar p')
substTyVarBndr = substTyVarBndrUsing substMonoKi

substTyVarBndrUsing
  :: SubstP p p'
  => (Subst p p' -> MonoKind p -> MonoKind p')
  -> Subst p p' -> TyVar p -> (Subst p p', TyVar p')
substTyVarBndrUsing subst_fn subst@(Subst {..}) old_var
  = assertPpr no_capture (pprTyVar old_var $$ pprTyVar new_var $$ ppr subst) $
    (Subst { tv_in_scope = tv_in_scope `extendInScopeSet` new_var
           , tv_env = new_env
           , .. }
    , new_var )
  where
    no_capture = not (new_var `elemVarSet` fstOf3 (shallowVarsOfTyVarEnv tv_env))

    new_var = uniqAway tv_in_scope $
              vacuous_set_tv_kind (subst_fn subst (varKind old_var)) old_var

    new_env = extendVarEnv tv_env old_var (mkTyVarTy new_var)
