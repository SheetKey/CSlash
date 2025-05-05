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

type KvSubstEnv = KiVarEnv MonoKind

emptySubst :: Subst
emptySubst = Subst emptyInScopeSet emptyVarEnv emptyVarEnv emptyVarEnv

mkEmptySubst :: InScopeSet -> Subst
mkEmptySubst in_scope = Subst in_scope emptyVarEnv emptyVarEnv emptyVarEnv

isEmptySubst :: Subst -> Bool
isEmptySubst (Subst _ id_env tv_env kv_env)
  = isEmptyVarEnv id_env && isEmptyVarEnv tv_env && isEmptyVarEnv kv_env

isEmptyKvSubst :: Subst -> Bool
isEmptyKvSubst (Subst _ _ _ kv_env) = isEmptyVarEnv kv_env

extendKvSubst :: Subst -> KindVar -> MonoKind -> Subst
extendKvSubst (Subst in_scope ids tvs kvs) kv ki
  = assertPpr (isKiVar kv) (text "extendKvSubst") $
    Subst in_scope ids tvs (extendVarEnv kvs kv ki)

extendKvSubstWithClone :: Subst -> KindVar -> KindVar -> Subst
extendKvSubstWithClone (Subst in_scope ids tvs kvs) kv kv'
  = Subst (extendInScopeSet in_scope kv')
          ids
          tvs
          (extendVarEnv kvs kv (mkKiVarMKi kv'))

zapSubst :: Subst -> Subst
zapSubst (Subst in_scope _ _ _) = Subst in_scope emptyVarEnv emptyVarEnv emptyVarEnv

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

isValidKiSubst :: Subst -> Bool
isValidKiSubst (Subst in_scope _ _ kenv) =
  (kenvFVs `varSetInScope` in_scope)
  where
    kenvFVs = shallowKiVarsOfMonoKiVarEnv kenv

checkValidKiSubst :: HasDebugCallStack => Subst -> [Kind] -> a -> a
checkValidKiSubst subst@(Subst in_scope _ _ kenv) kis a
  = assertPpr (isValidKiSubst subst)
              (text "in_scope" <+> ppr in_scope $$
               text "kenv" <+> ppr kenv $$
               text "kenvFVs" <+> ppr (shallowKiVarsOfMonoKiVarEnv kenv) $$
               text "kis" <+> ppr kis) $
    assertPpr kisFVsInScope
              (text "in_scope" <+> ppr in_scope $$
               text "kenv" <+> ppr kenv $$
               text "kis" <+> ppr kis $$
               text "needInScope" <+> ppr needInScope)
              a
  where
    substDomain = nonDetKeysUFM kenv
    needInScope = shallowKiVarsOfKinds kis `delListFromUniqSet_Directly` substDomain
    kisFVsInScope = needInScope `varSetInScope` in_scope

checkValidMonoKiSubst :: HasDebugCallStack => Subst -> [MonoKind] -> a -> a
checkValidMonoKiSubst subst@(Subst in_scope _ _ kenv) kis a
  = assertPpr (isValidKiSubst subst)
              (text "in_scope" <+> ppr in_scope $$
               text "kenv" <+> ppr kenv $$
               text "kenvFVs" <+> ppr (shallowKiVarsOfMonoKiVarEnv kenv) $$
               text "kis" <+> ppr kis) $
    assertPpr kisFVsInScope
              (text "in_scope" <+> ppr in_scope $$
               text "kenv" <+> ppr kenv $$
               text "kis" <+> ppr kis $$
               text "needInScope" <+> ppr needInScope)
              a
  where
    substDomain = nonDetKeysUFM kenv
    needInScope = shallowKiVarsOfMonoKinds kis `delListFromUniqSet_Directly` substDomain
    kisFVsInScope = needInScope `varSetInScope` in_scope

substKi :: HasDebugCallStack => Subst -> Kind -> Kind
substKi subst ki
  | isEmptyKvSubst subst = ki
  | otherwise = checkValidKiSubst subst [ki] $
                subst_ki subst ki

substMonoKi :: HasDebugCallStack => Subst -> MonoKind -> MonoKind
substMonoKi subst ki
  | isEmptyKvSubst subst = ki
  | otherwise = checkValidMonoKiSubst subst [ki] $
                subst_mono_ki subst ki

substMonoKis :: HasDebugCallStack => Subst -> [MonoKind] -> [MonoKind]
substMonoKis subst kis
  | isEmptyKvSubst subst = kis
  | otherwise = checkValidMonoKiSubst subst kis $ map (subst_mono_ki subst) kis

substKiUnchecked :: Subst -> Kind -> Kind
substKiUnchecked subst ki
  | isEmptyKvSubst subst = ki
  | otherwise = subst_ki subst ki

substMonoKiUnchecked :: Subst -> MonoKind -> MonoKind
substMonoKiUnchecked subst ki
  | isEmptyKvSubst subst = ki
  | otherwise = subst_mono_ki subst ki

subst_ki :: Subst -> Kind -> Kind
subst_ki subst ki = go ki
  where
    go (Mono ki) = Mono $! subst_mono_ki subst ki
    go (ForAllKi kv ki) = case substKiVarBndrUnchecked subst kv of
                            (subst', kv') -> (ForAllKi $! kv') $! (subst_ki subst' ki)

subst_mono_ki :: Subst -> MonoKind -> MonoKind
subst_mono_ki subst ki = go ki
  where
    go (KiVarKi kv) = substKiVar subst kv
    go ki@(FunKi { fk_arg = arg, fk_res = res })
      = let !arg' = go arg
            !res' = go res
        in ki { fk_arg = arg', fk_res = res' }
    go ki@(KiConApp kc kis) = (mkKiConApp $! kc) $! strictMap go kis

substKiVar :: Subst -> KindVar -> MonoKind
substKiVar (Subst _ _ _ kenv) kv
  = assert (isKiVar kv) $
    case lookupVarEnv kenv kv of
      Just ki -> ki
      Nothing -> KiVarKi kv

substKiVarBndrUnchecked :: Subst -> KindVar -> (Subst, KindVar)
substKiVarBndrUnchecked = substKiVarBndrUsing substKiUnchecked

substKiVarBndrUsing :: (Subst -> Kind -> Kind) -> Subst -> KindVar -> (Subst, KindVar)
substKiVarBndrUsing subst_fn subst@(Subst in_scope idenv tenv kenv) old_var
  = assertPpr _no_capture (ppr old_var $$ ppr new_var $$ ppr subst)
    $ assert (isKiVar old_var)
    (Subst (in_scope `extendInScopeSet` new_var) idenv tenv new_env, new_var)
  where
    new_env | no_change = delVarEnv kenv old_var
            | otherwise = extendVarEnv kenv old_var (KiVarKi new_var)

    _no_capture = not (new_var `elemVarSet` shallowKiVarsOfMonoKiVarEnv kenv)

    no_change = new_var == old_var

    new_var = uniqAway in_scope old_var
