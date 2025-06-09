{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Kind.Subst where

import Prelude hiding ((<>))

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

data KvSubst kv = KvSubst (InScopeSet kv) (KvSubstEnv kv)

type KvSubstEnv kv = MkVarEnv kv (MonoKind kv)

emptyKvSubstEnv :: KvSubstEnv kv
emptyKvSubstEnv = emptyVarEnv

emptyKvSubst :: KvSubst kv
emptyKvSubst = KvSubst emptyInScopeSet emptyVarEnv

mkEmptyKvSubst :: InScopeSet kv -> KvSubst kv
mkEmptyKvSubst in_scope = KvSubst in_scope emptyVarEnv

isEmptyKvSubst :: KvSubst kv -> Bool
isEmptyKvSubst (KvSubst _ kv_env)
  = isEmptyVarEnv kv_env

extendKvSubst :: IsVar kv => KvSubst kv -> kv -> MonoKind kv -> KvSubst kv
extendKvSubst (KvSubst in_scope kvs) kv ki
  = KvSubst in_scope (extendVarEnv kvs kv ki)

extendKvSubstWithClone :: IsVar kv => KvSubst kv -> kv -> kv -> KvSubst kv
extendKvSubstWithClone (KvSubst in_scope kvs) kv kv'
  = KvSubst (extendInScopeSet in_scope kv')
          (extendVarEnv kvs kv (mkKiVarKi kv'))

mkKvSubst :: InScopeSet kv -> KvSubstEnv kv -> KvSubst kv
mkKvSubst in_scope kenv = KvSubst in_scope kenv

zapKvSubst :: KvSubst kv -> KvSubst kv
zapKvSubst (KvSubst in_scope _) = KvSubst in_scope emptyVarEnv

instance Outputable kv => Outputable (KvSubst kv) where
  ppr (KvSubst in_scope kvs)
      =  text "<InScope =" <+> in_scope_doc
      $$ text " KvSubst   =" <+> ppr kvs
      <> char '>'
    where
      in_scope_doc = pprVarSet (getInScopeVars in_scope) (braces . fsep . map ppr)

{- **********************************************************************
*                                                                       *
                Performing kind substitutions
*                                                                       *
********************************************************************** -}

isValidKvSubst :: IsVar kv => KvSubst kv -> Bool
isValidKvSubst (KvSubst in_scope kenv) =
  (kenvFVs `varSetInScope` in_scope)
  where
    kenvFVs = varsOfMonoKiVarEnv kenv

checkValidKvSubst
  :: (HasDebugCallStack, IsVar kv)
  => KvSubst kv -> [Kind kv] -> a -> a
checkValidKvSubst subst@(KvSubst in_scope kenv) kis a
  = assertPpr (isValidKvSubst subst)
              (text "in_scope" <+> ppr in_scope $$
               text "kenv" <+> ppr kenv $$
               text "kenvFVs" <+> ppr (varsOfMonoKiVarEnv kenv) $$
               text "kis" <+> ppr kis) $
    assertPpr kisFVsInScope
              (text "in_scope" <+> ppr in_scope $$
               text "kenv" <+> ppr kenv $$
               text "kis" <+> ppr kis $$
               text "needInScope" <+> ppr needInScope)
              a
  where
    substDomain = nonDetKeysUFM kenv
    needInScope = varsOfKinds kis `delListFromUniqSet_Directly` substDomain
    kisFVsInScope = needInScope `varSetInScope` in_scope

checkValidMonoKvSubst
  :: (HasDebugCallStack, IsVar kv)
  => KvSubst kv -> [MonoKind kv] -> a -> a
checkValidMonoKvSubst subst@(KvSubst in_scope kenv) kis a
  = assertPpr (isValidKvSubst subst)
              (text "in_scope" <+> ppr in_scope $$
               text "kenv" <+> ppr kenv $$
               text "kenvFVs" <+> ppr (varsOfMonoKiVarEnv kenv) $$
               text "kis" <+> ppr kis) $
    assertPpr kisFVsInScope
              (text "in_scope" <+> ppr in_scope $$
               text "kenv" <+> ppr kenv $$
               text "kis" <+> ppr kis $$
               text "needInScope" <+> ppr needInScope)
              a
  where
    substDomain = nonDetKeysUFM kenv
    needInScope = varsOfMonoKinds kis `delListFromUniqSet_Directly` substDomain
    kisFVsInScope = needInScope `varSetInScope` in_scope

substKi
  :: (HasDebugCallStack, IsVar kv)
  => KvSubst kv -> Kind kv -> Kind kv
substKi subst ki
  | isEmptyKvSubst subst = ki
  | otherwise = checkValidKvSubst subst [ki] $
                subst_ki subst ki

substMonoKi
  :: (HasDebugCallStack, IsVar kv)
  => KvSubst kv -> MonoKind kv -> MonoKind kv
substMonoKi subst ki
  | isEmptyKvSubst subst = ki
  | otherwise = checkValidMonoKvSubst subst [ki] $
                subst_mono_ki subst ki

substMonoKis
  :: (HasDebugCallStack, IsVar kv)
  => KvSubst kv -> [MonoKind kv] -> [MonoKind kv]
substMonoKis subst kis
  | isEmptyKvSubst subst = kis
  | otherwise = checkValidMonoKvSubst subst kis $ map (subst_mono_ki subst) kis

substKiUnchecked :: IsVar kv => KvSubst kv -> Kind kv -> Kind kv
substKiUnchecked subst ki
  | isEmptyKvSubst subst = ki
  | otherwise = subst_ki subst ki

substMonoKiUnchecked :: IsVar kv => KvSubst kv -> MonoKind kv -> MonoKind kv
substMonoKiUnchecked subst ki
  | isEmptyKvSubst subst = ki
  | otherwise = subst_mono_ki subst ki

subst_ki :: IsVar kv => KvSubst kv -> Kind kv -> Kind kv
subst_ki subst ki = go ki
  where
    go (Mono ki) = Mono $! subst_mono_ki subst ki
    go (ForAllKi kv ki) = case substKiVarBndrUnchecked subst kv of
                            (subst', kv') -> (ForAllKi $! kv') $! (subst_ki subst' ki)

subst_mono_ki :: IsVar kv => KvSubst kv -> MonoKind kv -> MonoKind kv
subst_mono_ki subst ki = go ki
  where
    go (KiVarKi kv) = substKiVar subst kv
    go ki@(FunKi { fk_arg = arg, fk_res = res })
      = let !arg' = go arg
            !res' = go res
        in ki { fk_arg = arg', fk_res = res' }
    go ki@(KiConApp kc kis) = (mkKiConApp $! kc) $! strictMap go kis

substKiVar :: IsVar kv => KvSubst kv -> kv -> MonoKind kv
substKiVar (KvSubst _ kenv) kv
  = case lookupVarEnv kenv kv of
      Just ki -> ki
      Nothing -> KiVarKi kv

substKiVarBndrUnchecked :: IsVar kv => KvSubst kv -> kv -> (KvSubst kv, kv)
substKiVarBndrUnchecked = substKiVarBndrUsing substKiUnchecked

substKiVarBndrUsing
  :: IsVar kv => (KvSubst kv -> Kind kv -> Kind kv) -> KvSubst kv -> kv -> (KvSubst kv, kv)
substKiVarBndrUsing subst_fn subst@(KvSubst in_scope kenv) old_var
  = assertPpr _no_capture (ppr old_var $$ ppr new_var $$ ppr subst)
    (KvSubst (in_scope `extendInScopeSet` new_var) new_env, new_var)
  where
    new_env | no_change = delVarEnv kenv old_var
            | otherwise = extendVarEnv kenv old_var (KiVarKi new_var)

    _no_capture = not (new_var `elemVarSet` varsOfMonoKiVarEnv kenv)

    no_change = new_var == old_var

    new_var = uniqAway in_scope old_var
