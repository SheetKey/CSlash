{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Type.Tidy where

import CSlash.Cs.Pass

import CSlash.Data.FastString

import CSlash.Core.Kind
import CSlash.Core.Type.FVs (varsOfTypeList)
import CSlash.Core.Kind.FVs (varsOfKindList, varsOfMonoKindList, varsOfMonoKindsList)

import CSlash.Types.Name hiding (varName)
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Utils.Misc
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

tidyKiCoVarBndrs :: TidyEnv p -> [KiCoVar p] -> (TidyEnv p, [KiCoVar p])
tidyKiCoVarBndrs env kcvs = mapAccumL tidyKiCoVarBndr (avoidNameClashes kcvs env) kcvs

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

tidyTyVarOcc :: TidyEnv p -> TyVar p -> TyVar p
tidyTyVarOcc env@(_, subst, _, _) tv = case lookupVarEnv subst tv of
  Just tv' -> tv'
  Nothing -> updateVarKind (tidyMonoKind env) tv

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
tidyKiCoVarOcc :: TidyEnv p -> KiCoVar p -> KiCoVar p
tidyKiCoVarOcc env@(_, _, subst, _) kcv
  = case lookupVarEnv subst kcv of
      Nothing -> updateVarKind (tidyMonoKind env) kcv
      Just kcv' -> kcv'

tidyTcKiCoVarOcc :: TidyEnv Tc -> TcKiCoVar -> TcKiCoVar
tidyTcKiCoVarOcc env@(_, _, subst, _) cv = case lookupVarEnv subst (TcCoVar cv) of
  Just cv -> case cv of
               TcCoVar tccv -> tccv
               _ -> pprPanic "tidyTcKiCoVarOcc" (ppr env $$ ppr cv)
  Nothing -> updateVarKind (tidyMonoKind env) cv

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

tidyTcKiVarOcc :: TidyEnv Tc -> TcKiVar -> TcKiVar
tidyTcKiVarOcc env@(_, _, _, subst) kv = case lookupVarEnv subst (TcKiVar kv) of
  Just kv -> case kv of
    TcKiVar tckv -> tckv
    _ -> pprPanic "tidyTcKiVarOcc" (ppr env $$ ppr kv)
  Nothing -> kv

----------------
tidyTypes :: TidyEnv p -> [Type p] -> [Type p]
tidyTypes env tys = strictMap (tidyType env) tys

tidyType :: TidyEnv p -> Type p -> Type p
tidyType env (TyVarTy tv) = TyVarTy $! tidyTyVarOcc env tv
tidyType _ t@(TyConApp _ []) = t
tidyType env (TyConApp tycon tys) = TyConApp tycon $! tidyTypes env tys
tidyType env (AppTy fun arg) = (AppTy $! (tidyType env fun)) $! (tidyType env arg)
tidyType env (CastTy ty kco) = (CastTy $! tidyType env ty) $! (tidyKiCo env kco)
tidyType env (KindCoercion kco) = KindCoercion $! tidyKiCo env kco
tidyType env ty@(FunTy ki arg res)
  = let !ki' = tidyMonoKind env ki
        !arg' = tidyType env arg
        !res' = tidyType env res
    in FunTy ki' arg' res'
tidyType env ty@ForAllTy{} = tidyForAllType env ty
tidyType env ty@ForAllKiCo{} = tidyForAllType env ty
tidyType env ty@BigTyLamTy{} = tidyForAllType env ty
tidyType env ty@TyLamTy{} = tidyTyLamTy env ty
tidyType env (Embed ki) = Embed $! tidyMonoKind env ki
tidyType env other = warnPprTrace True "tidyType" (text "***************NOT TIDYING THE TYPE") other

tidyForAllType :: TidyEnv p -> Type p -> Type p
tidyForAllType env ty
  = (mkBigLamTys' $! kvs') $!
    (mkForAllKiCos' $! kcvs') $!
    (mkForAllTys' $! (zip tvs' vis)) $!
    tidyType body_env body_ty
  where
    (kvs, kcvs, tvs, vis, body_ty) = splitForAllBindersVis ty
    (env1, kvs') = tidyKiVarBndrs env kvs
    (env2, kcvs') = tidyKiCoVarBndrs env1 kcvs
    (body_env, tvs') = tidyTyVarBndrs env2 tvs

tidyTyLamTy :: TidyEnv p -> Type p -> Type p
tidyTyLamTy env ty
  = (mkTyLamTys' $! tvs') $! tidyType body_env body_ty
  where
    (tvs, body_ty) = splitTyLamTyBinders' ty
    (body_env, tvs') = tidyTyVarBndrs env tvs

splitTyLamTyBinders' :: Type p -> ([TyVar p], Type p)
splitTyLamTyBinders' ty = go ty []
  where
    go (TyLamTy tv ty) tvs = go ty (tv:tvs)
    go ty tvs = (reverse tvs, ty)

splitForAllBindersVis :: Type p -> ([KiVar p], [KiCoVar p], [TyVar p], [ForAllFlag], Type p)
splitForAllBindersVis ty
  = let (kvs, ty1) = splitBigLamTyBinders' ty
        (kcvs, ty2) = splitForAllKiCoVars' ty1
        (tvs, vis, ty3) = splitForAllForAllTyBinders' ty2
    in (kvs, kcvs, tvs, vis, ty3)

splitBigLamTyBinders' :: Type p -> ([KiVar p], Type p)
splitBigLamTyBinders' ty = go ty []
  where
    go (BigTyLamTy kv ty) kvs = (kv:kvs, ty)
    go ty kvs = (reverse kvs, ty)

splitForAllKiCoVars' :: Type p -> ([KiCoVar p], Type p)
splitForAllKiCoVars' ty = go ty []
  where
    go (ForAllKiCo kcv ty) kcvs = (kcv:kcvs, ty)
    go ty kcvs = (reverse kcvs, ty)

splitForAllForAllTyBinders' :: Type p -> ([TyVar p], [ForAllFlag], Type p)
splitForAllForAllTyBinders' ty = go ty [] []
  where
    go (ForAllTy (Bndr tv vis) ty) tvs viss = go ty (tv:tvs) (vis:viss)
    go ty tvs viss = (reverse tvs, reverse viss, ty)

mkTyLamTys' :: [TyVar p] -> Type p -> Type p
mkTyLamTys' kvs ty = foldr strictMkTyLamTy ty kvs
  where
    strictMkTyLamTy tv ty = (TyLamTy $! tv) $! ty

mkForAllTys' :: [(TyVar p, ForAllFlag)] -> Type p -> Type p
mkForAllTys' tvvs ty = foldr strictMkForAllTy ty tvvs
  where
    strictMkForAllTy (tv, vis) ty = (ForAllTy $! ((Bndr $! tv) $! vis)) $! ty
    
mkForAllKiCos' :: [KiCoVar p] -> Type p -> Type p
mkForAllKiCos' kvs ty = foldr strictMkForAllTy ty kvs
  where
    strictMkForAllTy kv ty = (ForAllKiCo $! kv) $! ty
    
mkBigLamTys' :: [KiVar p] -> Type p -> Type p
mkBigLamTys' kvs ty = foldr strictMkForAllTy ty kvs
  where
    strictMkForAllTy kv ty = (BigTyLamTy $! kv) $! ty

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

tidyKiCo :: TidyEnv p -> KindCoercion p -> KindCoercion p
tidyKiCo env co
  = go co
  where
    go (Refl ki) = Refl $! tidyMonoKind env ki
    go BI_U_A = BI_U_A
    go BI_A_L = BI_A_L
    go (BI_U_LTEQ ki) = BI_U_LTEQ $! tidyMonoKind env ki
    go (BI_LTEQ_L ki) = BI_LTEQ_L $! tidyMonoKind env ki
    go (LiftEq co) = LiftEq $! go co
    go (LiftLT co) = LiftLT $! go co
    go (FunCo afl afr co1 co2) = (FunCo afl afr $! go co1) $! go co2
    go (KiCoVarCo cv) = KiCoVarCo $! go_cv cv
    go (SymCo co) = SymCo $! go co
    go (TransCo co1 co2) = (TransCo $! go co1) $! go co2
    go (SelCo d co) = SelCo d $! go co
    go (HoleCo h) = HoleCo $! go_hole env h

    go_cv cv = tidyKiCoVarOcc env cv

    go_hole env (KindCoercionHole cv r) = (KindCoercionHole $! tidyTcKiCoVarOcc env cv) r

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
tidyMonoKind env (KiConApp kc) = KiConApp $ tidyKiCon env kc
tidyMonoKind env ki@(FunKi _ arg res) = let !arg' = tidyMonoKind env arg
                                            !res' = tidyMonoKind env res
                                        in ki { fk_arg = arg', fk_res = res' }

tidyKiCon :: TidyEnv p -> KiCon p -> KiCon p
tidyKiCon env (KiCon nm base rows) = KiCon nm (tidyMonoKind env base) (tidyRowSig env <$> rows)

tidyRowSig :: TidyEnv p -> RowSig p -> RowSig p
tidyRowSig env (RowTySig nm ty) = RowTySig nm (tidyType env ty)
tidyRowSig env (RowKiSig nm ki) = RowKiSig nm (tidyMonoKind env ki)
