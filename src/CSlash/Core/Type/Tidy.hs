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

tidyTyVarBndr :: TidyEnv p -> TyVar p -> (TidyEnv p, TyVar p)
tidyTyVarBndr env@(occ_env, tsubst, kcsubst, ksubst) var
  = case tidyOccName occ_env (getHelpfulOccName var) of
      (occ_env', occ') -> ((occ_env', tsubst', kcsubst, ksubst), var')
        where
          tsubst' = extendVarEnv tsubst var var'
          var' = updateVarKind (tidyMonoKind env) (setVarName var name')
          name' = tidyNameOcc name occ'
          name = varName var

tidyKiCoVarBndr :: TidyEnv p -> KiCoVar p -> (TidyEnv p, KiCoVar p)
tidyKiCoVarBndr env@(occ_env, tsubst, kcsubst, ksubst) var
  = case tidyOccName occ_env (getHelpfulOccName var) of
      (occ_env', occ') -> ((occ_env', tsubst, kcsubst', ksubst), var')
        where
          kcsubst' = extendVarEnv kcsubst var var'
          var' = updateVarKind (tidyMonoKind env) (setVarName var name')
          name' = tidyNameOcc name occ'
          name = varName var

tidyKiVarBndr :: TidyEnv p -> KiVar p -> (TidyEnv p, KiVar p)
tidyKiVarBndr tidy_env@(occ_env, tsubst, kcsubst, subst) var
  = case tidyOccName occ_env (getHelpfulOccName var) of
      (occ_env', occ') -> ((occ_env', tsubst, kcsubst, subst'), var')
        where
          subst' = extendVarEnv subst var var'
          var' = setVarName var name'
          name' = tidyNameOcc name occ'
          name = varName var

tidyTyVarBndrs :: TidyEnv p -> [TyVar p] -> (TidyEnv p, [TyVar p])
tidyTyVarBndrs env tvs = mapAccumL tidyTyVarBndr (avoidNameClashes tvs env) tvs

tidyKKiCoVarBndrs :: TidyEnv p -> [KiCoVar p] -> (TidyEnv p, [KiCoVar p])
tidyKKiCoVarBndrs env kcvs = mapAccumL tidyKiCoVarBndr (avoidNameClashes kcvs env) kcvs

tidyKiVarBndrs :: TidyEnv p -> [KiVar p] -> (TidyEnv p, [KiVar p])
tidyKiVarBndrs tidy_env vs = mapAccumL tidyKiVarBndr (avoidNameClashes vs tidy_env) vs

avoidNameClashes :: IsVar v => [v] -> TidyEnv p -> TidyEnv p
avoidNameClashes vs (occ_env, tsubst, kcsubst, ksubst)
  = (avoidClashesOccEnv occ_env occs, tsubst, kcsubst, ksubst)
  where occs = map getHelpfulOccName vs

getHelpfulOccName :: IsVar v => v -> OccName
getHelpfulOccName v
  | isSystemName name
  , isTcVar v
  = mkOccNameFS (occNameSpace occ) (occNameFS occ `appendFS` fsLit "0")
  | otherwise
  = occ
  where
    name = varName v
    occ = getOccName name

----------------
tidyFreeVars :: TidyEnv p -> ([TyVar p], [KiCoVar p], [KiVar p]) -> TidyEnv p
tidyFreeVars env vars = fst (tidyFreeVarsX env vars)

tidyFreeVarsX
  :: TidyEnv p
  -> ([TyVar p], [KiCoVar p], [KiVar p])
  -> (TidyEnv p, ([TyVar p], [KiCoVar p], [KiVar p]))
tidyFreeVarsX env (tvs, kcvs, kvs)
  = let (env1, kvs') = tidyFreeKiVarsX env kvs
        (env2, kcvs') = tidyFreeKiCoVarsX env1 kcvs
        (env3, tvs') = tidyFreeTyVarsX env2 tvs
    in (env3, (tvs', kcvs', kvs'))

----------------
tidyFreeTyVars :: TidyEnv p -> [TyVar p] -> TidyEnv p
tidyFreeTyVars tidy_env tyvars = fst (tidyFreeTyVarsX tidy_env tyvars)

tidyFreeTyVarsX :: TidyEnv p -> [TyVar p] -> (TidyEnv p, [TyVar p])
tidyFreeTyVarsX env tyvars = mapAccumL tidyFreeTyVarX env tyvars

tidyFreeTyVarX :: TidyEnv p -> TyVar p -> (TidyEnv p, TyVar p)
tidyFreeTyVarX env@(_, subst, _, _) tv = case lookupVarEnv subst tv of
                                        Just tyvar' -> (env, tyvar')
                                        Nothing -> tidyTyVarBndr env tv

tidyTcTyVarOcc :: TidyEnv Tc -> TcTyVar -> TcTyVar
tidyTcTyVarOcc env@(_, subst, _, _) tv = case lookupVarEnv subst (TcTyVar tv) of
  Just tv -> case tv of
               TcTyVar tctv -> tctv
               _ -> pprPanic "tidyTcTyVarOcc" (ppr env $$ ppr tv)
  Nothing -> updateVarKind (tidyMonoKind env) tv

----------------
tidyFreeKiCoVars :: TidyEnv p -> [KiCoVar p] -> TidyEnv p
tidyFreeKiCoVars tidy_env kcvs = fst (tidyFreeKiCoVarsX tidy_env kcvs)

tidyFreeKiCoVarsX :: TidyEnv p -> [KiCoVar p] -> (TidyEnv p, [KiCoVar p])
tidyFreeKiCoVarsX env kcvs = mapAccumL tidyFreeKiCoVarX env kcvs

tidyFreeKiCoVarX :: TidyEnv p -> KiCoVar p -> (TidyEnv p, KiCoVar p)
tidyFreeKiCoVarX env@(_, _, subst, _) kcv = case lookupVarEnv subst kcv of
                                              Just kcv' -> (env, kcv')
                                              Nothing -> tidyKiCoVarBndr env kcv

----------------
tidyFreeKiVars :: TidyEnv p -> [KiVar p] -> TidyEnv p
tidyFreeKiVars tidy_env vars = fst (tidyFreeKiVarsX tidy_env vars)

tidyFreeKiVarsX :: TidyEnv p -> [KiVar p] -> (TidyEnv p, [KiVar p])
tidyFreeKiVarsX env vars = mapAccumL tidyFreeKiVarX env vars

tidyFreeKiVarX :: TidyEnv p -> KiVar p -> (TidyEnv p, KiVar p)
tidyFreeKiVarX env@(_, _, _, subst) var = case lookupVarEnv subst var of
  Just var' -> (env, var')
  Nothing -> tidyKiVarBndr env var

tidyKiVarOcc :: TidyEnv p -> KiVar p -> KiVar p
tidyKiVarOcc env@(_, _, _, subst) v = case lookupVarEnv subst v of
                                        Nothing -> v
                                        Just v' -> v'
----------------

tidyType :: TidyEnv p -> Type p -> Type p
tidyType _ ty = warnPprTrace True "tidyType" (text "NOT TIDYING THE TYPE") ty

tidyKind :: TidyEnv p -> Kind p -> Kind p
tidyKind env (Mono mki) = Mono $ tidyMonoKind env mki
tidyKind env ki@(ForAllKi {}) = tidyForAllKind env ki

tidyTopKind :: Kind p -> Kind p
tidyTopKind ki = tidyKind emptyTidyEnv ki

tidyForAllKind :: TidyEnv p -> Kind p -> Kind p
tidyForAllKind env ki = (mkForAllKis' $! kvs') $! tidyMonoKind body_env body_ki
  where
    (kvs, body_ki) = splitForAllKiVars' ki
    (body_env, kvs') = tidyKiVarBndrs env kvs

mkForAllKis' :: [KiVar p] -> MonoKind p -> Kind p
mkForAllKis' kvs ki = foldr strictMkForAllKi (Mono ki) kvs
  where
    strictMkForAllKi kv ki = (ForAllKi $! kv) $! ki

splitForAllKiVars' :: Kind p -> ([KiVar p], MonoKind p)
splitForAllKiVars' ki = go ki []
  where
    go (ForAllKi kv ki) kvs = go ki (kv : kvs)
    go (Mono ki) kvs = (reverse kvs, ki)

tidyAvoiding :: [OccName] -> (TidyEnv p -> a -> TidyEnv p) -> a -> TidyEnv p
tidyAvoiding bound_var_avoids do_tidy thing
  = (occs' `delTidyOccEnvList` bound_var_avoids, tvars', kcvars', kvars')
  where
    (occs', tvars', kcvars', kvars') = do_tidy init_tidy_env thing
    init_tidy_env = mkEmptyTidyEnv (initTidyOccEnv bound_var_avoids)

trimTidyEnv :: TidyEnv p -> ([TyVar p], [KiCoVar p], [KiVar p]) -> TidyEnv p
trimTidyEnv (occ_env, tsubst, kcsubst, ksubst) (tvs, kcvs, kvs)
  = ( trimTidyOccEnv occ_env (map getOccName tvs ++ map getOccName kcvs ++ map getOccName kvs)
    , tsubst, kcsubst, ksubst )

tidyOpenTypeX :: TidyEnv p -> Type p -> (TidyEnv p, Type p)
tidyOpenTypeX env ty = (env1, tidyType inner_env ty)
  where
    free_vars = varsOfTypeList ty
    (env1, free_vars') = tidyFreeVarsX env free_vars
    inner_env = trimTidyEnv env1 free_vars'

tidyOpenType :: TidyEnv p -> Type p -> Type p
tidyOpenType env ty = snd (tidyOpenTypeX env ty)

tidyTopType :: Type p -> Type p
tidyTopType ty = tidyType emptyTidyEnv ty

tidyOpenMonoKinds :: TidyEnv p -> [MonoKind p] -> (TidyEnv p, [MonoKind p])
tidyOpenMonoKinds env kis = (env', tidyMonoKinds (trimmed_occ_env, tenv, kcenv, var_env) kis)
  where
    (env'@(_, tenv, kcenv, var_env), kvs') = tidyFreeKiVarsX env
                                             $ varsOfMonoKindsList kis
    trimmed_occ_env = initTidyOccEnv (map getOccName kvs')

tidyOpenMonoKind :: TidyEnv p -> MonoKind p -> (TidyEnv p, MonoKind p)
tidyOpenMonoKind env ki = case tidyOpenMonoKinds env [ki] of
                            (env', [ki']) -> (env', ki')
                            _ -> panic "tidyOpenMonoKind"

tidyMonoKinds :: TidyEnv p -> [MonoKind p] -> [MonoKind p]
tidyMonoKinds env kis = strictMap (tidyMonoKind env) kis

tidyMonoKind :: TidyEnv p -> MonoKind p -> MonoKind p
tidyMonoKind env (KiVarKi kv) = KiVarKi $! tidyKiVarOcc env kv
tidyMonoKind _ kc@(BIKi _) = kc
tidyMonoKind env (KiPredApp pred k1 k2) = let !k1' = tidyMonoKind env k1
                                              !k2' = tidyMonoKind env k2
                                          in KiPredApp pred k1' k2'
tidyMonoKind env ki@(FunKi _ arg res) = let !arg' = tidyMonoKind env arg
                                            !res' = tidyMonoKind env res
                                        in ki { fk_arg = arg', fk_res = res' }
