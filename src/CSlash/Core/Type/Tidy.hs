{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Type.Tidy where

import CSlash.Data.FastString

import CSlash.Core.Type.Rep
import CSlash.Core.Kind
import CSlash.Core.Type.FVs (varsOfTypeList)
import CSlash.Core.Kind.FVs (varsOfKindList, varsOfMonoKindList, varsOfMonoKindsList)

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

tidyTyVarBndr
  :: (VarHasKind tv kv, ToTcTyVarMaybe tv kv, ToTcKiVarMaybe kv)
  => MkTidyEnv tv kv -> tv -> (MkTidyEnv tv kv, tv)
tidyTyVarBndr env@(occ_env, tsubst, ksubst) var
  = case tidyOccName occ_env (getHelpfulOccNameTy var) of
      (occ_env', occ') -> ((occ_env', tsubst', ksubst), var')
        where
          tsubst' = extendVarEnv tsubst var var'
          var' = updateVarKind (tidyMonoKind env) (setVarName var name')
          name' = tidyNameOcc name occ'
          name = varName var

tidyKiVarBndrs :: ToTcKiVarMaybe kv => MkTidyEnv tv kv -> [kv] -> (MkTidyEnv tv kv, [kv])
tidyKiVarBndrs tidy_env vs = mapAccumL tidyKiVarBndr (avoidNameClashesKi vs tidy_env) vs

tidyKiVarBndr :: ToTcKiVarMaybe kv => MkTidyEnv tv kv -> kv -> (MkTidyEnv tv kv, kv)
tidyKiVarBndr tidy_env@(occ_env, tsubst, subst) var
  = case tidyOccName occ_env (getHelpfulOccNameKi var) of
      (occ_env', occ') -> ((occ_env', tsubst, subst'), var')
        where
          subst' = extendVarEnv subst var var'
          var' = setVarName var name'
          name' = tidyNameOcc name occ'
          name = varName var

avoidNameClashesKi :: ToTcKiVarMaybe kv => [kv] -> MkTidyEnv tv kv -> MkTidyEnv tv kv
avoidNameClashesKi vs (occ_env, tsubst, ksubst)
  = (avoidClashesOccEnv occ_env occs, tsubst, ksubst)
  where occs = map getHelpfulOccNameKi vs

getHelpfulOccNameTy :: (ToTcTyVarMaybe tv kv) => tv -> OccName
getHelpfulOccNameTy tv
  | isSystemName name
  , Just _ <- toTcTyVar_maybe tv
  = mkTyVarOccFS (occNameFS occ `appendFS` fsLit "0")
  | otherwise
  = occ
  where
    name = varName tv
    occ = getOccName name

getHelpfulOccNameKi :: ToTcKiVarMaybe kv => kv -> OccName
getHelpfulOccNameKi v
  | isSystemName name
  , Just _ <- toTcKiVar_maybe v
  = mkKiVarOccFS (occNameFS occ `appendFS` fsLit "0")
  | otherwise
  = occ
  where
    name = varName v
    occ = getOccName name

-- tidyForAllTyBinder
--   :: TidyEnv -> VarBndr (AnyTyVar AnyKiVar) vis -> (TidyEnv, VarBndr (AnyTyVar AnyKiVar) vis)
-- tidyForAllTyBinder tidy_env (Bndr tv vis) = (tidy_env', Bndr tv' vis)
--   where (tidy_env', tv') = tidyVarBndr tidy_env tv

-- tidyForAllTyBinders
--   :: TidyEnv -> [VarBndr (AnyTyVar AnyKiVar) vis] -> (TidyEnv, [VarBndr (AnyTyVar AnyKiVar) vis])
-- tidyForAllTyBinders tidy_env tvbs
--   = mapAccumL tidyForAllTyBinder (avoidNameClashes (binderVars tvbs) tidy_env) tvbs

-- tidyTyLamTyBinder :: TidyEnv -> AnyTyVar AnyKiVar -> (TidyEnv, AnyTyVar AnyKiVar)
-- tidyTyLamTyBinder tidy_env tv = (tidy_env', tv')
--   where (tidy_env', tv') = tidyVarBndr tidy_env tv

-- tidyBigLamTyBinder :: TidyEnv -> AnyKiVar -> (TidyEnv, AnyKiVar)
-- tidyBigLamTyBinder tidy_env kv = (tidy_env', kv')
--   where (tidy_env', kv') = tidyVarBndr tidy_env kv

-- tidyTyLamTyBinders :: TidyEnv -> [AnyTyVar AnyKiVar] -> (TidyEnv, [AnyTyVar AnyKiVar])
-- tidyTyLamTyBinders tidy_env tvbs
--   = mapAccumL tidyTyLamTyBinder (avoidNameClashes tvbs tidy_env) tvbs

-- tidyBigLamTyBinders :: TidyEnv -> [AnyKiVar] -> (TidyEnv, [AnyKiVar])
-- tidyBigLamTyBinders tidy_env kvbs
--   = mapAccumL tidyBigLamTyBinder (avoidNameClashes kvbs tidy_env) kvbs

tidyFreeTyKiVars
  :: (VarHasKind tv kv, ToTcTyVarMaybe tv kv, ToTcKiVarMaybe kv)
  => MkTidyEnv tv kv -> ([tv], [kv]) -> MkTidyEnv tv kv
tidyFreeTyKiVars env (tvs, kvs) = tidyFreeTyVars (tidyFreeKiVars env kvs) tvs

tidyFreeTyVars
  :: (VarHasKind tv kv, ToTcTyVarMaybe tv kv, ToTcKiVarMaybe kv)
  => MkTidyEnv tv kv -> [tv] -> MkTidyEnv tv kv
tidyFreeTyVars tidy_env tyvars = fst (tidyFreeTyVarsX tidy_env tyvars)

tidyFreeTyVarsX
  :: (VarHasKind tv kv, ToTcTyVarMaybe tv kv, ToTcKiVarMaybe kv)
  => MkTidyEnv tv kv -> [tv] -> (MkTidyEnv tv kv, [tv])
tidyFreeTyVarsX env tyvars = mapAccumL tidyFreeTyVarX env tyvars

tidyFreeTyVarX
  :: (VarHasKind tv kv, ToTcTyVarMaybe tv kv, ToTcKiVarMaybe kv)
  => MkTidyEnv tv kv -> tv -> (MkTidyEnv tv kv, tv)
tidyFreeTyVarX env@(_, subst, _) tv = case lookupVarEnv subst tv of
                                        Just tyvar' -> (env, tyvar')
                                        Nothing -> tidyTyVarBndr env tv

tidyFreeKiVars :: ToTcKiVarMaybe kv => MkTidyEnv tv kv -> [kv] -> MkTidyEnv tv kv
tidyFreeKiVars tidy_env vars = fst (tidyOpenKiVars tidy_env vars)

tidyOpenKiVars :: ToTcKiVarMaybe kv => MkTidyEnv tv kv -> [kv] -> (MkTidyEnv tv kv, [kv])
tidyOpenKiVars env vars = mapAccumL tidyOpenKiVar env vars

tidyOpenKiVar :: ToTcKiVarMaybe kv => MkTidyEnv tv kv -> kv -> (MkTidyEnv tv kv, kv)
tidyOpenKiVar env@(_, _, subst) var = case lookupVarEnv subst var of
  Just var' -> (env, var')
  Nothing -> tidyKiVarBndr env var

tidyKiVarOcc :: ToTcKiVarMaybe kv => MkTidyEnv tv kv -> kv -> kv
tidyKiVarOcc env@(_, _, subst) v = case lookupVarEnv subst v of
                                  Nothing -> v
                                  Just v' -> v'

tidyType :: MkTidyEnv tv kv -> Type tv kv -> Type tv kv
tidyType _ ty = warnPprTrace True "tidyType" (text "NOT TIDYING THE TYPE") ty

tidyKind :: ToTcKiVarMaybe kv => MkTidyEnv tv kv -> Kind kv -> Kind kv
tidyKind env (Mono mki) = Mono $ tidyMonoKind env mki
tidyKind env ki@(ForAllKi {}) = tidyForAllKind env ki

tidyForAllKind :: ToTcKiVarMaybe kv => MkTidyEnv tv kv -> Kind kv -> Kind kv
tidyForAllKind env ki = (mkForAllKis' $! kvs') $! tidyMonoKind body_env body_ki
  where
    (kvs, body_ki) = splitForAllKiVars' ki
    (body_env, kvs') = tidyKiVarBndrs env kvs

mkForAllKis' :: [kv] -> MonoKind kv -> Kind kv
mkForAllKis' kvs ki = foldr strictMkForAllKi (Mono ki) kvs
  where
    strictMkForAllKi kv ki = (ForAllKi $! kv) $! ki

splitForAllKiVars' :: Kind kv -> ([kv], MonoKind kv)
splitForAllKiVars' ki = go ki []
  where
    go (ForAllKi kv ki) kvs = go ki (kv : kvs)
    go (Mono ki) kvs = (reverse kvs, ki)

tidyAvoiding :: [OccName] -> (MkTidyEnv tv kv -> a -> MkTidyEnv tv kv) -> a -> MkTidyEnv tv kv
tidyAvoiding bound_var_avoids do_tidy thing
  = (occs' `delTidyOccEnvList` bound_var_avoids, tvars', kvars')
  where
    (occs', tvars', kvars') = do_tidy init_tidy_env thing
    init_tidy_env = mkEmptyTidyEnv (initTidyOccEnv bound_var_avoids)

tidyOpenMonoKinds
  :: ToTcKiVarMaybe kv => MkTidyEnv tv kv -> [MonoKind kv] -> (MkTidyEnv tv kv, [MonoKind kv])
tidyOpenMonoKinds env kis = (env', tidyMonoKinds (trimmed_occ_env, tenv, var_env) kis)
  where
    (env'@(_, tenv, var_env), kvs') = tidyOpenKiVars env
                                $ varsOfMonoKindsList kis
    trimmed_occ_env = initTidyOccEnv (map getOccName kvs')

tidyOpenMonoKind
  :: ToTcKiVarMaybe kv => MkTidyEnv tv kv -> MonoKind kv -> (MkTidyEnv tv kv, MonoKind kv)
tidyOpenMonoKind env ki = case tidyOpenMonoKinds env [ki] of
                            (env', [ki']) -> (env', ki')
                            _ -> panic "tidyOpenMonoKind"

tidyMonoKinds :: ToTcKiVarMaybe kv => MkTidyEnv tv kv -> [MonoKind kv] -> [MonoKind kv]
tidyMonoKinds env kis = strictMap (tidyMonoKind env) kis

tidyMonoKind :: ToTcKiVarMaybe kv => MkTidyEnv tv kv -> MonoKind kv -> MonoKind kv
tidyMonoKind env (KiVarKi kv) = KiVarKi $! tidyKiVarOcc env kv
tidyMonoKind _ kc@(BIKi _) = kc
tidyMonoKind env (KiPredApp pred k1 k2) = let !k1' = tidyMonoKind env k1
                                              !k2' = tidyMonoKind env k2
                                          in KiPredApp pred k1' k2'
tidyMonoKind env ki@(FunKi _ arg res) = let !arg' = tidyMonoKind env arg
                                            !res' = tidyMonoKind env res
                                        in ki { fk_arg = arg', fk_res = res' }
