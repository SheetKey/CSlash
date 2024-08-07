{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Kind.Subst where

import {-# SOURCE #-} CSlash.Core ( CoreExpr )
import {-# SOURCE #-} CSlash.Core.Ppr ()

import CSlash.Core.Type.Rep
import CSlash.Core.Kind
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

data Subst = Subst InScopeSet IdSubstEnv TvSubstEnv KvSubstEnv

type IdSubstEnv = IdEnv CoreExpr

type TvSubstEnv = TyVarEnv Type

type KvSubstEnv = KdVarEnv Kind

emptySubst :: Subst
emptySubst = Subst emptyInScopeSet emptyVarEnv emptyVarEnv emptyVarEnv

mkEmptySubst :: InScopeSet -> Subst
mkEmptySubst in_scope = Subst in_scope emptyVarEnv emptyVarEnv emptyVarEnv

isEmptySubst :: Subst -> Bool
isEmptySubst (Subst _ id_env tv_env kv_env)
  = isEmptyVarEnv id_env && isEmptyVarEnv tv_env && isEmptyVarEnv kv_env

isEmptyKvSubst :: Subst -> Bool
isEmptyKvSubst (Subst _ _ _ kv_env) = isEmptyVarEnv kv_env

instance Outputable Subst where
  ppr (Subst in_scope ids tvs kvs)
      =  text "<InScope =" <+> in_scope_doc
      $$ text "IdSubst    =" <+> ppr ids
      $$ text "TvSubst    =" <+> ppr tvs
      $$ text "KvSubst    =" <+> ppr kvs
    where
      in_scope_doc = pprVarSet (getInScopeVars in_scope) (braces . fsep . map ppr)

{- **********************************************************************
*                                                                       *
                Performing kind substitutions
*                                                                       *
********************************************************************** -}

isValidKdSubst :: Subst -> Bool
isValidKdSubst (Subst in_scope _ _ kenv) =
  (kenvFVs `varSetInScope` in_scope)
  where
    kenvFVs = shallowKdVarsOfKdVarEnv kenv

checkValidKdSubst :: HasDebugCallStack => Subst -> [Kind] -> a -> a
checkValidKdSubst subst@(Subst in_scope _ _ kenv) kds a
  = assertPpr (isValidKdSubst subst)
              (text "in_scope" <+> ppr in_scope $$
               text "kenv" <+> ppr kenv $$
               text "kenvFVs" <+> ppr (shallowKdVarsOfKdVarEnv kenv) $$
               text "kds" <+> ppr kds) $
    assertPpr kdsFVsInScope
              (text "in_scope" <+> ppr in_scope $$
               text "kenv" <+> ppr kenv $$
               text "kds" <+> ppr kds $$
               text "needInScope" <+> ppr needInScope)
              a
  where
    substDomain = nonDetKeysUFM kenv
    needInScope = shallowKdVarsOfKinds kds `delListFromUniqSet_Directly` substDomain
    kdsFVsInScope = needInScope `varSetInScope` in_scope

substKd :: HasDebugCallStack => Subst -> Kind -> Kind
substKd subst kd
  | isEmptyKvSubst subst = kd
  | otherwise = checkValidKdSubst subst [kd] $
                subst_kd subst kd

subst_kd :: Subst -> Kind -> Kind
subst_kd subst kd
  = go kd
  where
    go (KdVarKd kv) = substKdVar subst kv
    go kd@(FunKd { kft_arg = arg, kft_res = res })
      = let !arg' = go arg
            !res' = go res
        in kd { kft_arg = arg', kft_res = res' }
    go (KdContext rels) = KdContext $ go_rel <$> rels
    go UKd = UKd
    go AKd = AKd
    go LKd = LKd

    go_rel (LTKd k1 k2) = LTKd (go k1) (go k2)
    go_rel (LTEQKd k1 k2) = LTEQKd (go k1) (go k2)

substKdVar :: Subst -> KindVar -> Kind
substKdVar (Subst _ _ _ kenv) kv
  = assert (isKdVar kv) $
    case lookupVarEnv kenv kv of
      Just kd -> kd
      Nothing -> KdVarKd kv
