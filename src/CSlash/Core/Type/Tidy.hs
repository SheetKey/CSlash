{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Type.Tidy where

import CSlash.Data.FastString

import CSlash.Core.Type.Rep
import CSlash.Core.Kind
import CSlash.Core.Type.FVs (tyKiVarsOfTypeList)
import CSlash.Core.Kind.FVs (kiVarsOfKindList, kiVarsOfMonoKindList
                            , kiCoVarsOfMonoKindsWellScoped)

import CSlash.Types.Name hiding (varName)
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Utils.Misc (strictMap)
import CSlash.Utils.Trace
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Data.List (mapAccumL)

{- *********************************************************************
*                                                                      *
            TidyType
*                                                                      *
********************************************************************* -}

tidyVarBndrs :: TidyEnv -> [Var] -> (TidyEnv, [Var])
tidyVarBndrs tidy_env vs = mapAccumL tidyVarBndr (avoidNameClashes vs tidy_env) vs

tidyVarBndr :: TidyEnv -> Var -> (TidyEnv, Var)
tidyVarBndr tidy_env@(occ_env, subst) var
  = case tidyOccName occ_env (getHelpfulOccName var) of
      (occ_env', occ') -> ((occ_env', subst'), var')
        where
          subst' = extendVarEnv subst var var'
          var' = updateVarKindSafe (tidyMonoKind tidy_env) (setVarName var name')
          name' = tidyNameOcc name occ'
          name = varName var

avoidNameClashes :: [TypeVar] -> TidyEnv -> TidyEnv
avoidNameClashes tvs (occ_env, subst)
  = (avoidClashesOccEnv occ_env occs, subst)
  where occs = map getHelpfulOccName tvs

getHelpfulOccName :: Var -> OccName
getHelpfulOccName v
  | isSystemName name, isTcTyVar v
  = mkTyVarOccFS (occNameFS occ `appendFS` fsLit "0")
  | isSystemName name, isTcKiVar v
  = mkKiVarOccFS (occNameFS occ `appendFS` fsLit "0")
  | otherwise
  = occ
  where
    name = varName v
    occ = getOccName name

tidyForAllTyBinder :: TidyEnv -> VarBndr TypeVar vis -> (TidyEnv, VarBndr TypeVar vis)
tidyForAllTyBinder tidy_env (Bndr tv vis) = (tidy_env', Bndr tv' vis)
  where (tidy_env', tv') = tidyVarBndr tidy_env tv

tidyForAllTyBinders :: TidyEnv -> [VarBndr TypeVar vis] -> (TidyEnv, [VarBndr TypeVar vis])
tidyForAllTyBinders tidy_env tvbs
  = mapAccumL tidyForAllTyBinder (avoidNameClashes (binderVars tvbs) tidy_env) tvbs

tidyTyLamTyBinder :: TidyEnv -> TypeVar -> (TidyEnv, TypeVar)
tidyTyLamTyBinder tidy_env tv = (tidy_env', tv')
  where (tidy_env', tv') = tidyVarBndr tidy_env tv

tidyBigLamTyBinder :: TidyEnv -> KindVar -> (TidyEnv, KindVar)
tidyBigLamTyBinder tidy_env kv = (tidy_env', kv')
  where (tidy_env', kv') = tidyVarBndr tidy_env kv

tidyTyLamTyBinders :: TidyEnv -> [TypeVar] -> (TidyEnv, [TypeVar])
tidyTyLamTyBinders tidy_env tvbs
  = mapAccumL tidyTyLamTyBinder (avoidNameClashes tvbs tidy_env) tvbs

tidyBigLamTyBinders :: TidyEnv -> [KindVar] -> (TidyEnv, [KindVar])
tidyBigLamTyBinders tidy_env kvbs
  = mapAccumL tidyBigLamTyBinder (avoidNameClashes kvbs tidy_env) kvbs

tidyFreeTyKiVars :: TidyEnv -> [Var] -> TidyEnv
tidyFreeTyKiVars tidy_env vars = fst (tidyOpenTyKiVars tidy_env vars)

tidyOpenTyKiVars :: TidyEnv -> [Var] -> (TidyEnv, [Var])
tidyOpenTyKiVars env vars = mapAccumL tidyOpenTyKiVar env vars

tidyOpenTyKiVar :: TidyEnv -> Var -> (TidyEnv, Var)
tidyOpenTyKiVar env@(_, subst) var = case lookupVarEnv subst var of
  Just var' -> (env, var')
  Nothing -> let env' = if isTyVar var
                        then tidyFreeTyKiVars env (kiVarsOfMonoKindList (tyVarKind var))
                        else env
             in tidyVarBndr env' var

tidyTyKiVarOcc :: TidyEnv -> Var -> Var
tidyTyKiVarOcc env@(_, subst) v = case lookupVarEnv subst v of
                                    Nothing -> updateVarKindSafe (tidyMonoKind env) v
                                    Just v' -> v'

tidyType :: TidyEnv -> Type -> Type
tidyType _ ty = warnPprTrace True "tidyType" (text "NOT TIDYING THE TYPE") ty

tidyKind :: TidyEnv -> Kind -> Kind
tidyKind env (Mono mki) = Mono $ tidyMonoKind env mki
tidyKind env ki@(ForAllKi {}) = tidyForAllKind env ki

tidyForAllKind :: TidyEnv -> Kind -> Kind
tidyForAllKind env ki = (mkForAllKis' $! kvs') $! tidyMonoKind body_env body_ki
  where
    (kvs, body_ki) = splitForAllKiVars' ki
    (body_env, kvs') = tidyVarBndrs env kvs

mkForAllKis' :: [KindVar] -> MonoKind -> Kind
mkForAllKis' kvs ki = foldr strictMkForAllKi (Mono ki) kvs
  where
    strictMkForAllKi kv ki = (ForAllKi $! kv) $! ki

splitForAllKiVars' :: Kind -> ([KindVar], MonoKind)
splitForAllKiVars' ki = go ki []
  where
    go (ForAllKi kv ki) kvs = go ki (kv : kvs)
    go (Mono ki) kvs = (reverse kvs, ki)

tidyOpenMonoKinds :: TidyEnv -> [MonoKind] -> (TidyEnv, [MonoKind])
tidyOpenMonoKinds env kis = (env', tidyMonoKinds (trimmed_occ_env, var_env) kis)
  where
    (env'@(_, var_env), kvs') = tidyOpenTyKiVars env
                                $ kiCoVarsOfMonoKindsWellScoped kis
    trimmed_occ_env = initTidyOccEnv (map getOccName kvs')

tidyOpenMonoKind :: TidyEnv -> MonoKind -> (TidyEnv, MonoKind)
tidyOpenMonoKind env ki = case tidyOpenMonoKinds env [ki] of
                            (env', [ki']) -> (env', ki')
                            _ -> panic "tidyOpenMonoKind"

tidyMonoKinds :: TidyEnv -> [MonoKind] -> [MonoKind]
tidyMonoKinds env kis = strictMap (tidyMonoKind env) kis

tidyMonoKind :: TidyEnv -> MonoKind -> MonoKind
tidyMonoKind env (KiVarKi kv) = KiVarKi $! tidyTyKiVarOcc env kv
tidyMonoKind _ kc@(KiConApp _ []) = kc
tidyMonoKind env (KiConApp kc kis) = KiConApp kc $! tidyMonoKinds env kis
tidyMonoKind env ki@(FunKi _ arg res) = let !arg' = tidyMonoKind env arg
                                            !res' = tidyMonoKind env res
                                        in ki { fk_arg = arg', fk_res = res' }
