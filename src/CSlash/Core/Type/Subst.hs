{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Type.Subst where

import Prelude hiding ((<>))

import {-# SOURCE #-} CSlash.Core.Type ( mkAppTy, mkTyConApp, mkCastTy )
import {-# SOURCE #-} CSlash.Core.Type.Ppr ( pprTyVar )
import {-# SOURCE #-} CSlash.Core ( CoreExpr )

import CSlash.Core.Type.Rep
import CSlash.Core.Type.FVs
import CSlash.Core.Kind
import CSlash.Core.Kind.Subst
import CSlash.Core.Kind.FVs

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

{- **********************************************************************
*                                                                       *
                Substitutions
*                                                                       *
********************************************************************** -}

data TvSubst tv kv = TvSubst (InScopeSet tv) (TvSubstEnv tv kv) (KvSubst kv)

type TvSubstEnv tv kv = MkVarEnv tv (Type tv kv)

emptyTvSubstEnv :: TvSubstEnv tv kv
emptyTvSubstEnv = emptyVarEnv

emptyTvSubst :: TvSubst tv kv
emptyTvSubst = TvSubst emptyInScopeSet emptyVarEnv emptyKvSubst

mkEmptyTvSubst :: (InScopeSet tv, InScopeSet kv) -> TvSubst tv kv
mkEmptyTvSubst (in_scope, k_in_scope) = TvSubst in_scope emptyVarEnv (mkEmptyKvSubst k_in_scope)

isEmptyTvSubst :: TvSubst tv kv -> Bool
isEmptyTvSubst (TvSubst _ tv_env _) = isEmptyVarEnv tv_env

extendTvSubst :: IsVar tv => TvSubst tv kv -> tv -> Type tv kv -> TvSubst tv kv
extendTvSubst (TvSubst in_scope tvs ksubst) tv ty
  = TvSubst in_scope (extendVarEnv tvs tv ty) ksubst

instance VarHasKind tv kv => Outputable (TvSubst tv kv) where
  ppr (TvSubst in_scope tvs ksubst)
      =  text "<InScope =" <+> in_scope_doc
      $$ text " TvSubst   =" <+> ppr tvs
      $$ text " KvSubst   =" <+> ppr ksubst
      <> char '>'
    where
      in_scope_doc = pprVarSet (getInScopeVars in_scope) (braces . fsep . map ppr)

{- **********************************************************************
*                                                                       *
                Performing type substitutions
*                                                                       *
********************************************************************** -}

isValidTvSubst :: VarHasKind tv kv => TvSubst tv kv -> Bool
isValidTvSubst (TvSubst in_scope tenv ksubst@(KvSubst k_in_scope _)) =
  (tenvFVs `varSetInScope` in_scope) &&
  (kenvFVs `varSetInScope` k_in_scope) &&
  (isValidKvSubst ksubst)
  where
    (tenvFVs, kcvenvFVs, kenvFVs) = shallowVarsOfTyVarEnv tenv

checkValidTvSubst
  :: (HasDebugCallStack, VarHasKind tv kv)
  => TvSubst tv kv -> [Type tv kv] -> a -> a
checkValidTvSubst subst@(TvSubst in_scope tenv ksubst@(KvSubst k_in_scope kenv)) tys a
  = assertPpr (isValidTvSubst subst)
              (text "in_scope" <+> ppr in_scope $$
               text "tenv" <+> ppr tenv $$
               text "tenvFVs" <+> ppr (shallowVarsOfTyVarEnv tenv) $$
               text "ksubst" <+> ppr ksubst $$
               text "tys" <+> ppr tys) $
    assertPpr tysFVsInScope
              (text "in_scope" <+> ppr in_scope $$
               text "tenv" <+> ppr tenv $$
               text "tys" <+> ppr tys $$
               text "needInScope" <+> ppr needInScope) $
    assertPpr tysKFVsInScope
              (text "k_in_scope" <+> ppr k_in_scope $$
               text "kenv" <+> ppr kenv $$
               text "tys" <+> ppr tys $$
               text "needInScopeKi" <+> ppr needInScopeKi)
              a
  where
    substDomain = nonDetKeysUFM tenv
    kvsubstDomain = nonDetKeysUFM kenv
    (tenvFVs, kcvenvFVs, kenvFVs) = shallowVarsOfTypes tys
    needInScope = tenvFVs `delListFromUniqSet_Directly` substDomain
    needInScopeKi = kenvFVs `delListFromUniqSet_Directly` kvsubstDomain
    tysFVsInScope = needInScope `varSetInScope` in_scope
    tysKFVsInScope = needInScopeKi `varSetInScope` k_in_scope

substTy
  :: (HasDebugCallStack, VarHasKind tv kv)
  => TvSubst tv kv -> Type tv kv -> Type tv kv
substTy subst ty
  | isEmptyTvSubst subst = ty
  | otherwise = checkValidTvSubst subst [ty] $
                subst_ty subst ty

substTyUnchecked :: VarHasKind tv kv => TvSubst tv kv -> Type tv kv -> Type tv kv
substTyUnchecked subst ty
  | isEmptyTvSubst subst = ty
  | otherwise = subst_ty subst ty

subst_ty
  :: VarHasKind tv kv
  => TvSubst tv kv -> Type tv kv -> Type tv kv
subst_ty subst@(TvSubst is tenv ksubst) ty = go ty
  where
    go (TyVarTy tv) = substTyVar subst tv
    go (AppTy fun arg) = (mkAppTy $! (go fun)) $! (go arg)
    go (TyLamTy tv ty)
      = case substTyVarBndrUnchecked subst tv of
          (subst', tv') -> (TyLamTy $! tv') $! (subst_ty subst' ty)
    go (BigTyLamTy kv ty)
      = case substKiVarBndrUnchecked ksubst kv of
          (ksubst', kv') -> (BigTyLamTy $! kv') $! (subst_ty (TvSubst is tenv ksubst') ty)
    go ty@(TyConApp tc []) = tc `seq` ty
    go (TyConApp tc tys) = (mkTyConApp $! tc) $! strictMap go tys
    go ty@(FunTy { ft_kind = kind, ft_arg = arg, ft_res = res })
      = let !kind' = substMonoKi ksubst kind
            !arg' = go arg
            !res' = go res
        in ty { ft_kind = kind', ft_arg = arg', ft_res = res' }
    go (ForAllTy (Bndr tv vis) ty)
      = case substTyVarBndrUnchecked subst tv of
          (subst', tv') -> (ForAllTy $! ((Bndr $! tv') vis))
                                     $! (subst_ty subst' ty)
    go (Embed mki) = Embed $! substMonoKi ksubst mki
    go (CastTy ty co) = (mkCastTy $! (go ty)) $! co
    go co@(KindCoercion {}) = pprPanic "subst_ty" (ppr co)

substTyVar :: (IsVar tv) => TvSubst tv kv -> tv -> Type tv kv
substTyVar (TvSubst _ tenv _) tv
  = case lookupVarEnv tenv tv of
      Just ty -> ty
      Nothing -> TyVarTy tv

substTyVarBndrUnchecked :: VarHasKind tv kv => TvSubst tv kv -> tv -> (TvSubst tv kv, tv)
substTyVarBndrUnchecked = substTyVarBndrUsing substMonoKi

substTyVarBndrUsing
  :: VarHasKind tv kv
  => (KvSubst kv -> MonoKind kv -> MonoKind kv)
  -> TvSubst tv kv -> tv -> (TvSubst tv kv, tv)
substTyVarBndrUsing subst_fn subst@(TvSubst in_scope tenv ksubst) old_var
  = assertPpr _no_capture (pprTyVar old_var $$ pprTyVar new_var $$ ppr subst) $
    (TvSubst (in_scope `extendInScopeSet` new_var) new_env ksubst, new_var)
  where
    new_env | no_change = delVarEnv tenv old_var
            | otherwise = extendVarEnv tenv old_var (TyVarTy new_var)

    _no_capture = not (new_var `elemVarSet` fstOf3 (shallowVarsOfTyVarEnv tenv))

    old_ki = varKind old_var
    no_kind_change = noFreeVarsOfMonoKind old_ki
    no_change = no_kind_change && (new_var == old_var)

    new_var | no_kind_change = uniqAway in_scope old_var
            | otherwise = uniqAway in_scope $
                          setVarKind old_var (subst_fn ksubst old_ki)
