{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Type.Tidy where

import CSlash.Cs.Pass

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

tidyTyVarBndr :: HasPass p p' => TidyEnv p -> TyVar p -> (TidyEnv p, TyVar p)
tidyTyVarBndr env@(occ_env, tsubst, ksubst) var
  = case tidyOccName occ_env (getHelpfulOccNameTy var) of
      (occ_env', occ') -> ((occ_env', tsubst', ksubst), var')
        where
          tsubst' = extendVarEnv tsubst var var'
          var' = updateVarKind (tidyMonoKind env) (setVarName var name')
          name' = tidyNameOcc name occ'
          name = varName var

tidyTyVarBndrs :: HasPass p p' => TidyEnv p -> [TyVar p] -> (TidyEnv p, [TyVar p])
tidyTyVarBndrs env tvs = mapAccumL tidyTyVarBndr (avoidNameClashesTy tvs env) tvs

tidyKiVarBndrs :: HasPass p p' => TidyEnv p -> [KiVar p] -> (TidyEnv p, [KiVar p])
tidyKiVarBndrs tidy_env vs = mapAccumL tidyKiVarBndr (avoidNameClashesKi vs tidy_env) vs

tidyKiVarBndr :: HasPass p p' => TidyEnv p -> KiVar p -> (TidyEnv p, KiVar p)
tidyKiVarBndr tidy_env@(occ_env, tsubst, subst) var
  = case tidyOccName occ_env (getHelpfulOccNameKi var) of
      (occ_env', occ') -> ((occ_env', tsubst, subst'), var')
        where
          subst' = extendVarEnv subst var var'
          var' = setVarName var name'
          name' = tidyNameOcc name occ'
          name = varName var

avoidNameClashesKi :: HasPass p p' => [KiVar p] -> TidyEnv p -> TidyEnv p
avoidNameClashesKi vs (occ_env, tsubst, ksubst)
  = (avoidClashesOccEnv occ_env occs, tsubst, ksubst)
  where occs = map getHelpfulOccNameKi vs

avoidNameClashesTy :: HasPass p p' => [TyVar p] -> TidyEnv p -> TidyEnv p
avoidNameClashesTy vs (occ_env, tsubst, ksubst)
  = (avoidClashesOccEnv occ_env occs, tsubst, ksubst)
  where occs = map getHelpfulOccNameTy vs

getHelpfulOccNameTy :: HasPass p p' => TyVar p -> OccName
getHelpfulOccNameTy tv
  | isSystemName name
  , Just _ <- toTcTyVar_maybe tv
  = mkTyVarOccFS (occNameFS occ `appendFS` fsLit "0")
  | otherwise
  = occ
  where
    name = varName tv
    occ = getOccName name

getHelpfulOccNameKi :: KiVar p -> OccName
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

tidyFreeTyKiVars :: HasPass p p' => TidyEnv p -> ([TyVar p], [KiVar p]) -> TidyEnv p
tidyFreeTyKiVars env (tvs, kvs) = tidyFreeTyVars (tidyFreeKiVars env kvs) tvs

tidyFreeTyKiVarsX :: HasPass p p' => TidyEnv p -> ([TyVar p], [KiVar p]) -> (TidyEnv p, ([TyVar p], [KiVar p]))
tidyFreeTyKiVarsX env (tvs, kvs)
  = let (env1, kvs') = tidyOpenKiVars env kvs
        (env2, tvs') = tidyFreeTyVarsX env1 tvs
    in (env2, (tvs', kvs'))

tidyFreeTyVars :: HasPass p p' => TidyEnv p -> [TyVar p] -> TidyEnv p
tidyFreeTyVars tidy_env tyvars = fst (tidyFreeTyVarsX tidy_env tyvars)

tidyFreeTyVarsX :: HasPass p p' => TidyEnv p -> [TyVar p] -> (TidyEnv p, [TyVar p])
tidyFreeTyVarsX env tyvars = mapAccumL tidyFreeTyVarX env tyvars

tidyFreeTyVarX :: HasPass p p' => TidyEnv p -> TyVar p -> (TidyEnv p, TyVar p)
tidyFreeTyVarX env@(_, subst, _) tv = case lookupVarEnv subst tv of
                                        Just tyvar' -> (env, tyvar')
                                        Nothing -> tidyTyVarBndr env tv

tidyTcTyVarOcc :: TidyEnv Tc -> TcTyVar -> TcTyVar
tidyTcTyVarOcc env@(_, subst, _) tv = case lookupVarEnv subst (TcTyVar tv) of
  Just tv -> case tv of
               TcTyVar tctv -> tctv
               _ -> pprPanic "tidyTcTyVarOcc" (ppr env $$ ppr tv)
  Nothing -> updateVarKind (tidyMonoKind env) tv

tidyFreeKiVars :: HasPass p p' => TidyEnv p -> [KiVar p] -> TidyEnv p
tidyFreeKiVars tidy_env vars = fst (tidyOpenKiVars tidy_env vars)

-- rename this func
tidyOpenKiVars :: HasPass p p' => TidyEnv p -> [KiVar p] -> (TidyEnv p, [KiVar p])
tidyOpenKiVars env vars = mapAccumL tidyOpenKiVar env vars

tidyOpenKiVar :: HasPass p p' => TidyEnv p -> KiVar p -> (TidyEnv p, KiVar p)
tidyOpenKiVar env@(_, _, subst) var = case lookupVarEnv subst var of
  Just var' -> (env, var')
  Nothing -> tidyKiVarBndr env var

tidyKiVarOcc :: HasPass p p' => TidyEnv p -> KiVar p -> KiVar p
tidyKiVarOcc env@(_, _, subst) v = case lookupVarEnv subst v of
                                  Nothing -> v
                                  Just v' -> v'

tidyType :: HasPass p p' => TidyEnv p -> Type p -> Type p
tidyType _ ty = warnPprTrace True "tidyType" (text "NOT TIDYING THE TYPE") ty

tidyKind :: HasPass p p' => TidyEnv p -> Kind p -> Kind p
tidyKind env (Mono mki) = Mono $ tidyMonoKind env mki
tidyKind env ki@(ForAllKi {}) = tidyForAllKind env ki

tidyTopKind :: HasPass p p' => Kind p -> Kind p
tidyTopKind ki = tidyKind emptyTidyEnv ki

tidyForAllKind :: HasPass p p' => TidyEnv p -> Kind p -> Kind p
tidyForAllKind env ki = (mkForAllKis' $! kvs') $! tidyMonoKind body_env body_ki
  where
    (kvs, body_ki) = splitForAllKiVars' ki
    (body_env, kvs') = tidyKiVarBndrs env kvs

mkForAllKis' :: HasPass p p' => [KiVar p] -> MonoKind p -> Kind p
mkForAllKis' kvs ki = foldr strictMkForAllKi (Mono ki) kvs
  where
    strictMkForAllKi kv ki = (ForAllKi $! kv) $! ki

splitForAllKiVars' :: HasPass p p' => Kind p -> ([KiVar p], MonoKind p)
splitForAllKiVars' ki = go ki []
  where
    go (ForAllKi kv ki) kvs = go ki (kv : kvs)
    go (Mono ki) kvs = (reverse kvs, ki)

tidyAvoiding :: HasPass p p' => [OccName] -> (TidyEnv p -> a -> TidyEnv p) -> a -> TidyEnv p
tidyAvoiding bound_var_avoids do_tidy thing
  = (occs' `delTidyOccEnvList` bound_var_avoids, tvars', kvars')
  where
    (occs', tvars', kvars') = do_tidy init_tidy_env thing
    init_tidy_env = mkEmptyTidyEnv (initTidyOccEnv bound_var_avoids)

trimTidyEnvTyKi :: HasPass p p' => TidyEnv p -> ([TyVar p], [KiVar p]) -> TidyEnv p
trimTidyEnvTyKi (occ_env, tsubst, ksubst) (tvs, kvs)
  = (trimTidyOccEnv occ_env (map getOccName tvs ++ map getOccName kvs), tsubst, ksubst)

tidyOpenTypeX :: HasPass p p' => TidyEnv p -> Type p -> (TidyEnv p, Type p)
tidyOpenTypeX env ty = (env1, tidyType inner_env ty)
  where
    free_tkvs = varsOfTypeList ty
    (env1, free_tkvs') = tidyFreeTyKiVarsX env free_tkvs
    inner_env = trimTidyEnvTyKi env1 free_tkvs'

tidyOpenType :: HasPass p p' => TidyEnv p -> Type p -> Type p
tidyOpenType env ty = snd (tidyOpenTypeX env ty)

tidyTopType :: HasPass p p' => Type p -> Type p
tidyTopType ty = tidyType emptyTidyEnv ty

tidyOpenMonoKinds :: HasPass p p' => TidyEnv p -> [MonoKind p] -> (TidyEnv p, [MonoKind p])
tidyOpenMonoKinds env kis = (env', tidyMonoKinds (trimmed_occ_env, tenv, var_env) kis)
  where
    (env'@(_, tenv, var_env), kvs') = tidyOpenKiVars env
                                $ varsOfMonoKindsList kis
    trimmed_occ_env = initTidyOccEnv (map getOccName kvs')

tidyOpenMonoKind :: HasPass p p' => TidyEnv p -> MonoKind p -> (TidyEnv p, MonoKind p)
tidyOpenMonoKind env ki = case tidyOpenMonoKinds env [ki] of
                            (env', [ki']) -> (env', ki')
                            _ -> panic "tidyOpenMonoKind"

tidyMonoKinds :: HasPass p p' => TidyEnv p -> [MonoKind p] -> [MonoKind p]
tidyMonoKinds env kis = strictMap (tidyMonoKind env) kis

tidyMonoKind :: HasPass p p' => TidyEnv p -> MonoKind p -> MonoKind p
tidyMonoKind env (KiVarKi kv) = KiVarKi $! tidyKiVarOcc env kv
tidyMonoKind _ kc@(BIKi _) = kc
tidyMonoKind env (KiPredApp pred k1 k2) = let !k1' = tidyMonoKind env k1
                                              !k2' = tidyMonoKind env k2
                                          in KiPredApp pred k1' k2'
tidyMonoKind env ki@(FunKi _ arg res) = let !arg' = tidyMonoKind env arg
                                            !res' = tidyMonoKind env res
                                        in ki { fk_arg = arg', fk_res = res' }
