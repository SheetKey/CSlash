{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Type.Subst where

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
                Performing type substitutions
*                                                                       *
********************************************************************** -}

isEmptyTvSubst :: Subst -> Bool
isEmptyTvSubst (Subst _ _ tv_env _) = isEmptyVarEnv tv_env

extendTvSubst :: Subst -> TypeVar -> Type -> Subst
extendTvSubst (Subst in_scope ids tvs kvs) tv ty
  = assert (isTyVar tv) $
    Subst in_scope ids (extendVarEnv tvs tv ty) kvs

{- **********************************************************************
*                                                                       *
                Performing type substitutions
*                                                                       *
********************************************************************** -}

isValidTvSubst :: Subst -> Bool
isValidTvSubst (Subst in_scope _ tenv kenv) =
  (tenvFVs `varSetInScope` in_scope) &&
  (kenvFVs `varSetInScope` in_scope)
  where
    tenvFVs = shallowTyVarsOfTyVarEnv tenv
    kenvFVs = shallowKiVarsOfMonoKiVarEnv kenv

checkValidSubst :: HasDebugCallStack => Subst -> [Type] -> a -> a
checkValidSubst subst@(Subst in_scope _ tenv _) tys a
  = assertPpr (isValidTvSubst subst)
              (text "in_scope" <+> ppr in_scope $$
               text "tenv" <+> ppr tenv $$
               text "tenvFVs" <+> ppr (shallowTyVarsOfTyVarEnv tenv) $$
               text "tys" <+> ppr tys) $
    assertPpr tysFVsInScope
              (text "in_scope" <+> ppr in_scope $$
               text "tenv" <+> ppr tenv $$
               text "tys" <+> ppr tys $$
               text "needInScope" <+> ppr needInScope)
              a
  where
    substDomain = nonDetKeysUFM tenv
    needInScope = shallowTyVarsOfTypes tys `delListFromUniqSet_Directly` substDomain
    tysFVsInScope = needInScope `varSetInScope` in_scope

substTy :: HasDebugCallStack => Subst -> Type -> Type
substTy subst ty
  | isEmptyTvSubst subst = ty
  | otherwise = checkValidSubst subst [ty] $
                subst_ty subst ty

substTyUnchecked :: Subst -> Type -> Type
substTyUnchecked subst ty
  | isEmptyTvSubst subst = ty
  | otherwise = subst_ty subst ty

subst_ty :: Subst -> Type -> Type
subst_ty subst ty = go ty
  where
    go (TyVarTy tv) = substTyVar subst tv
    go (AppTy fun arg) = (mkAppTy $! (go fun)) $! (go arg)
    go (TyLamTy tv ty)
      = case substTyVarBndrUnchecked subst tv of
          (subst', tv') -> (TyLamTy $! tv') $! (subst_ty subst' ty)
    go (BigTyLamTy kv ty)
      = case substKiVarBndrUnchecked subst kv of
          (subst', kv') -> (BigTyLamTy $! kv') $! (subst_ty subst' ty)
    go ty@(TyConApp tc []) = tc `seq` ty
    go (TyConApp tc tys) = (mkTyConApp $! tc) $! strictMap go tys
    go ty@(FunTy { ft_kind = kind, ft_arg = arg, ft_res = res })
      = let !kind' = substMonoKi subst kind
            !arg' = go arg
            !res' = go res
        in ty { ft_kind = kind', ft_arg = arg', ft_res = res' }
    go (ForAllTy (Bndr tv vis) ty)
      = case substTyVarBndrUnchecked subst tv of
          (subst', tv') -> (ForAllTy $! ((Bndr $! tv') vis))
                                     $! (subst_ty subst' ty)
    go (Embed mki) = Embed $! substMonoKi subst mki
    go (CastTy ty co) = (mkCastTy $! (go ty)) $! co

substTyVar :: Subst -> TypeVar -> Type
substTyVar (Subst _ _ tenv _) tv
  = assert (isTyVar tv) $
    case lookupVarEnv tenv tv of
      Just ty -> ty
      Nothing -> TyVarTy tv

substTyVarBndrUnchecked :: Subst -> TypeVar -> (Subst, TypeVar)
substTyVarBndrUnchecked = substTyVarBndrUsing substMonoKi

substTyVarBndrUsing
  :: (Subst -> MonoKind -> MonoKind)
  -> Subst -> TypeVar -> (Subst, TypeVar)
substTyVarBndrUsing subst_fn subst@(Subst in_scope idenv tenv kenv) old_var
  = assertPpr _no_capture (pprTyVar old_var $$ pprTyVar new_var $$ ppr subst) $
    assert (isTyVar old_var)
    (Subst (in_scope `extendInScopeSet` new_var) idenv new_env kenv, new_var)
  where
    new_env | no_change = delVarEnv tenv old_var
            | otherwise = extendVarEnv tenv old_var (TyVarTy new_var)

    _no_capture = not (new_var `elemVarSet` shallowTyVarsOfTyVarEnv tenv)

    old_ki = varKind old_var
    no_kind_change = noFreeVarsOfMonoKind old_ki
    no_change = no_kind_change && (new_var == old_var)

    new_var | no_kind_change = uniqAway in_scope old_var
            | otherwise = uniqAway in_scope $
                          setTyVarKind old_var (subst_fn subst old_ki)
