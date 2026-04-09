{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}

module CSlash.Core.Unify where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Name( Name, mkSysTvName, mkSystemVarName )
import CSlash.Core.Type
import CSlash.Core.Type.Compare
import CSlash.Core.Type.FVs
import CSlash.Core.TyCon
import CSlash.Core.Kind
import CSlash.Core.Kind.Compare
import CSlash.Core.Kind.FVs
import CSlash.Core.Subst
import CSlash.Utils.FV( FV, fvVarAcc )
import CSlash.Utils.Misc
import CSlash.Data.Pair
import CSlash.Utils.Outputable
import CSlash.Types.Unique
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Set
import GHC.Exts( oneShot )
import CSlash.Utils.Panic
import CSlash.Data.FastString

import Data.List ( mapAccumL )
import Control.Monad
import qualified Data.Semigroup as S

type KiBindFun p = KiVar p -> MonoKind p -> BindFlag
type KiCoBindFun p = KiCoVar p -> KindCoercion p -> BindFlag
type TyBindFun p = TyVar p -> Type p -> BindFlag

type BindFuns p = (TyBindFun p, KiCoBindFun p, KiBindFun p)

tcMatchTy :: Type Zk -> Type Zk -> Maybe CoreSubst
tcMatchTy ty1 ty2 = tcMatchTys [ty1] [ty2]

tcMatchTys :: [Type Zk] -> [Type Zk] -> Maybe CoreSubst
tcMatchTys tys1 tys2 = tc_match_tys alwaysBindFuns False tys1 tys2

tc_match_tys
  :: BindFuns Zk
  -> Bool
  -> [Type Zk]
  -> [Type Zk]
  -> Maybe (Subst Zk Zk)
tc_match_tys bind_me match_kis tys1 tys2
  = tc_match_tys_x bind_me match_kis empty_subst tys1 tys2
  where
    empty_subst = mkEmptySubst (varsOfTypes tys1) (varsOfTypes tys2)

tc_match_tys_x
  :: BindFuns Zk
  -> Bool
  -> CoreSubst
  -> [Type Zk]
  -> [Type Zk]
  -> Maybe CoreSubst
tc_match_tys_x bind_mes match_kis Subst{..} tys1 tys2
  = case tc_unify_tys bind_mes False False match_kis rn_envs subst_envs tys1 tys2 of
      Unifiable (tv_env', kcv_env', kv_env')
        -> Just $ Subst { tv_env = tv_env'
                        , kcv_env = kcv_env'
                        , kv_env = kv_env'
                        , .. }
      _ -> Nothing
  where
    rn_envs = (mkRnEnv2 tv_in_scope, mkRnEnv2 kcv_in_scope, mkRnEnv2 kv_in_scope)
    subst_envs = (tv_env, kcv_env, kv_env)

alwaysBindFuns :: BindFuns p
alwaysBindFuns = (\_ _ -> BindMe, \_ _ -> BindMe, \_ _ -> BindMe)

{- *********************************************************************
*                                                                      *
                Type Unification
*                                                                      *
********************************************************************* -}

type RnEnv2s p = (RnEnv2 (TyVar p), RnEnv2 (KiCoVar p), RnEnv2 (KiVar p))
type SubstEnvs p = (TvSubstEnv p p, KCvSubstEnv p p, KvSubstEnv p p)

tc_unify_tys
  :: BindFuns Zk
  -> Bool
  -> Bool
  -> Bool
  -> RnEnv2s Zk
  -> SubstEnvs Zk
  -> [Type Zk]
  -> [Type Zk]
  -> UnifyResultM (SubstEnvs Zk)
tc_unify_tys bind_fns unif inj_check match_kis rn_envs subst_envs tys1 tys2
  = initUM subst_envs $ do
      when match_kis $
        unify_kis env kis1 kis2
      unify_tys env tys1 tys2
      getSubstEnvs
  where
    env = UMEnv { um_unif = unif
                , um_inj_tf = inj_check
                , um_rn_envs = rn_envs
                , um_skols = (emptyVarSet, emptyVarSet, emptyVarSet)
                , um_bind_fun = bind_fns
                }
    kis1 = map typeMonoKind tys1
    kis2 = map typeMonoKind tys2

{- *********************************************************************
*                                                                      *
                Kind Unification
*                                                                      *
********************************************************************* -}

type UnifyResult p = UnifyResultM (Subst p p)

data UnifyResultM a
  = Unifiable a
  | MaybeApart MaybeApartReason a
  | SurelyApart
  deriving Functor

data MaybeApartReason
  = MARInfinite
  | MARKindVsConstraint

instance Outputable MaybeApartReason where
  ppr MARInfinite = text "MARInfinite"
  ppr MARKindVsConstraint = text "MARKindVsConstraint"

instance Semigroup MaybeApartReason where
  MARInfinite <> _ = MARInfinite
  MARKindVsConstraint <> r = r

instance Applicative UnifyResultM where
  pure = Unifiable
  (<*>) = ap

instance Monad UnifyResultM where
  SurelyApart >>= _ = SurelyApart
  MaybeApart r1 x >>= f = case f x of
    Unifiable y -> MaybeApart r1 y
    MaybeApart r2 y -> MaybeApart (r1 S.<> r2) y
    SurelyApart -> SurelyApart
  Unifiable x >>= f = f x

tcUnifyKisFG :: KiBindFun Tc -> [MonoKind Tc] -> [MonoKind Tc] -> UnifyResult Tc
tcUnifyKisFG bind_fn kis1 kis2 = tc_unify_kis_fg bind_fn kis1 kis2

tc_unify_kis_fg :: KiBindFun Tc -> [MonoKind Tc] -> [MonoKind Tc] -> UnifyResult Tc
tc_unify_kis_fg bind_fn kis1 kis2 = do
  env <- tc_unify_kis bind_fn True False rn_env emptyVarEnv kis1 kis2
  return $ niFixSubst in_scope env
  where
    in_scope = mkInScopeSet $ varsOfMonoKinds kis1 `unionVarSet` varsOfMonoKinds kis2
    rn_env = mkRnEnv2 in_scope

tc_unify_kis
  :: KiBindFun Tc
  -> Bool
  -> Bool
  -> RnEnv2 (KiVar Tc)
  -> KvSubstEnv Tc Tc
  -> [MonoKind Tc]
  -> [MonoKind Tc]
  -> UnifyResultM (KvSubstEnv Tc Tc)
tc_unify_kis bind_fn unif inj_check rn_env kv_env kis1 kis2
  = initUM (emptyVarEnv, emptyVarEnv, kv_env) $ do
  unify_kis env kis1 kis2
  getKvSubstEnv
  where
    env = UMEnv { um_bind_fun = (panic "bind_fn", panic "bind_fn", bind_fn)
                , um_skols = (emptyVarSet, emptyVarSet, emptyVarSet)
                , um_unif = unif
                , um_inj_tf = inj_check
                , um_rn_envs = (mkRnEnv2 emptyInScopeSet, mkRnEnv2 emptyInScopeSet, rn_env) }

{- *********************************************************************
*                                                                      *
                Non-idempotent substitution
*                                                                      *
********************************************************************* -}

niFixSubst :: InScopeSet (KiVar Tc) -> KvSubstEnv Tc Tc -> Subst Tc Tc
niFixSubst in_scope kenv
  | not_fixpoint = niFixSubst in_scope (mapVarEnv (substMonoKi subst) kenv)
  | otherwise = subst
  where
    range_fvs = fvsOfMonoKinds (nonDetEltsUFM kenv)

    range_kvs = fst $ fvVarAcc range_fvs 

    not_fixpoint = any in_domain range_kvs
    in_domain kv = kv `elemVarEnv` kenv

    free_kvs = filterOut in_domain range_kvs

    subst = foldl' add_free_kv (mkKvSubst in_scope kenv) free_kvs

    add_free_kv subst kv = extendKvSubst subst kv (mkKiVarKi kv)

niSubstKvSet :: HasPass p p' => KvSubstEnv p p -> KiVarSet p -> KiVarSet p
niSubstKvSet subst kvs = nonDetStrictFoldUniqSet (unionVarSet . get) emptyVarSet kvs
  where
    get kv
      | Just ki <- lookupVarEnv subst kv
      = niSubstKvSet subst (varsOfMonoKind ki)
      | otherwise
      = unitVarSet kv

niSubstTvSet :: HasPass p p' => TvSubstEnv p p -> TyVarSet p -> TyVarSet p
niSubstTvSet tsubst tvs = nonDetStrictFoldUniqSet (unionVarSet . get) emptyVarSet tvs
  where
    get tv
      | Just ty <- lookupVarEnv tsubst tv
      = niSubstTvSet tsubst (fstOf3 $ varsOfType ty)
      | otherwise
      = unitVarSet tv

{- *********************************************************************
*                                                                      *
                unify_ty: the main workhorse
*                                                                      *
********************************************************************* -}

unify_ty :: HasPass p p' => UMEnv p -> Type p -> Type p -> KindCoercion p -> UM p ()
unify_ty _ (TyConApp tc1 []) (TyConApp tc2 []) _
  | tc1 == tc2
  = return ()
  
unify_ty env ty1 ty2 kco
  | Just ty1' <- coreView ty1 = unify_ty env ty1' ty2 kco
  | Just ty2' <- coreView ty2 = unify_ty env ty1 ty2' kco
  | CastTy ty1' co <- ty1 = if um_unif env
                            then panic "um_unif"
                            else do subst <- getSubst env
                                    let co' = substKiCo subst co
                                    unify_ty env ty1' ty2 (co' `mkTransKiCo` kco)
  | CastTy ty2' co <- ty2 = unify_ty env ty1 ty2' (kco `mkTransKiCo` mkSymKiCo co)

unify_ty env (TyVarTy tv1) ty2 kco = uTyVar env tv1 ty2 kco
unify_ty env ty1 (TyVarTy tv2) kco
  | um_unif env
  = uTyVar (umSwapRn env) tv2 ty1 (mkSymKiCo kco)

unify_ty env ty1 ty2 _
  | Just (tc1, tys1) <- splitTyConApp_maybe ty1
  , Just (tc2, tys2) <- splitTyConApp_maybe ty2
  , tc1 == tc2
  = do massertPpr (isInjectiveTyCon tc1) (ppr tc1)
       unify_tys env tys1 tys2

unify_ty env (AppTy ty1a ty1b) ty2 _
  | Just (ty2a, ty2b) <- tcSplitAppTyNoView_maybe ty2
  = unify_ty_app env ty1a [ty1b] ty2a [ty2b]

unify_ty env ty1 (AppTy ty2a ty2b) _
  | Just (ty1a, ty1b) <- tcSplitAppTyNoView_maybe ty1
  = unify_ty_app env ty1a [ty1b] ty2a [ty2b]

unify_ty env (ForAllTy (Bndr tv1 _) ty1) (ForAllTy (Bndr tv2 _) ty2) kco = do
  unify_ki env (varKind tv1) (varKind tv2)
  let env' = umRnTvBndr2 env tv1 tv2
  unify_ty env' ty1 ty2 kco

unify_ty env (ForAllKiCo kcv1 ty1) (ForAllKiCo kcv2 ty2) kco = do
  unify_ki env (varKind kcv1) (varKind kcv2)
  let env' = umRnKCvBndr2 env kcv1 kcv2
  unify_ty env' ty1 ty2 kco

unify_ty env (BigTyLamTy kv1 ty1) (BigTyLamTy kv2 ty2) kco = do 
  let env' = umRnKvBndr2 env kv1 kv2
  unify_ty env' ty1 ty2 kco
  
unify_ty env (KindCoercion co1) (KindCoercion co2) kco = do panic "unfinished2"

unify_ty env (Embed ki1) (Embed ki2) _
  = unify_ki env ki1 ki2

unify_ty _ FunTy{} FunTy{} _ = panic "unreachable"
unify_ty _ _ TyLamTy{} _ = panic "unreachable"
unify_ty _ _ TyLamTy{} _ = panic "unreachable"

unify_ty _ _ _ _ = surelyApart

unify_ty_app :: HasPass p p' => UMEnv p -> Type p -> [Type p] -> Type p -> [Type p] -> UM p ()
unify_ty_app env ty1 ty1args ty2 ty2args
  | Just (ty1', ty1a) <- splitAppTyNoView_maybe ty1
  , Just (ty2', ty2a) <- splitAppTyNoView_maybe ty2
  = unify_ty_app env ty1' (ty1a : ty1args) ty2' (ty2a : ty2args)

  | otherwise
  = do let ki1 = typeMonoKind ty1 -- TODO: may cause problems!
           ki2 = typeMonoKind ty2
       unify_ki env ki1 ki2
       unify_ty env ty1 ty2 (mkReflKiCo ki2)
       unify_tys env ty1args ty2args

unify_tys :: HasPass p p' => UMEnv p -> [Type p] -> [Type p] -> UM p ()
unify_tys env orig_xs orig_ys
  = go orig_xs orig_ys
  where
    go [] [] = return ()
    go (x:xs) (y:ys) = do
      unify_ty env x y (mkReflKiCo $ typeMonoKind y)
      go xs ys
    go _ _ = surelyApart

uTyVar :: HasPass p p' => UMEnv p -> TyVar p -> Type p -> KindCoercion p -> UM p ()
uTyVar env tv1 ty kco = do
  let tv1' = umRnTvOccL env tv1
  subst <- getTvSubstEnv
  case lookupVarEnv subst tv1' of
    Just ty' | um_unif env -> unify_ty env ty' ty kco
             | otherwise -> unless ((ty' `mkCastTy` kco) `tcEqType` ty) $ surelyApart
    Nothing -> uUnrefinedTy env tv1' ty ty kco

uUnrefinedTy :: HasPass p p' => UMEnv p -> TyVar p -> Type p -> Type p -> KindCoercion p -> UM p ()
uUnrefinedTy env tv1' ty2 ty2' kco
  | Just ty2'' <- coreView ty2'
  = uUnrefinedTy env tv1' ty2 ty2'' kco

  | TyVarTy tv2 <- ty2'
  = do let tv2' = umRnTvOccR env tv2
       unless (tv1' == tv2' && um_unif env) $ do
         subst <- getTvSubstEnv
         case lookupVarEnv subst tv2 of
           Just ty' | um_unif env -> uUnrefinedTy env tv1' ty' ty' kco
           _ -> do let rhs1 = ty2 `mkCastTy` mkSymKiCo kco
                       rhs2 = ty1 `mkCastTy` kco
                       b1 = tvBindFlag env tv1' rhs1
                       b2 = tvBindFlag env tv2' rhs2
                       ty1 = mkTyVarTy tv1'
                   case (b1, b2) of
                     (BindMe, _) -> bindTv env tv1' rhs1
                     (_, BindMe) | um_unif env -> bindTv (umSwapRn env) tv2 rhs2

                     _ | tv1' == tv2' -> return ()

                     _ -> surelyApart

uUnrefinedTy env tv1' ty2 _ kco = case tvBindFlag env tv1' rhs of
  Apart -> surelyApart
  BindMe -> bindTv env tv1' rhs
  where rhs = ty2 `mkCastTy` mkSymKiCo kco

bindTv :: HasPass p p' => UMEnv p -> TyVar p -> Type p -> UM p ()
bindTv env tv1 ty2 = do
  let free_tvs2 = fstOf3 $ varsOfType ty2

  checkRnEnvT env free_tvs2

  occurs <- occursCheckT env tv1 free_tvs2

  if occurs
    then maybeApart MARInfinite
    else extendTvEnv tv1 ty2

occursCheckT :: HasPass p p' => UMEnv p -> TyVar p -> TyVarSet p -> UM p Bool
occursCheckT env tv free_tvs
  | um_unif env
  = do tsubst <- getTvSubstEnv
       return (tv `elemVarSet` niSubstTvSet tsubst free_tvs)
  | otherwise
  = return False

unify_ki :: HasPass p p' => UMEnv p -> MonoKind p -> MonoKind p -> UM p ()

unify_ki _ (BIKi k1) (BIKi k2)
  | k1 == k2
  = return ()

unify_ki env (KiVarKi kv1) ki2 = uKiVar env kv1 ki2

unify_ki env ki1 (KiVarKi kv2) = uKiVar (umSwapRn env) kv2 ki1

unify_ki env ki1 ki2
  | KiPredApp kc1 _ _ <- ki1
  , KiPredApp kc2 _ _ <- ki2
  --, kc1 == kc2
  = panic "unify_kis env kis1 kis2"

  | FunKi {} <- ki1
  , FunKi {} <- ki2
  = maybeApart MARKindVsConstraint

unify_ki _ _ _ = surelyApart

unify_kis :: HasPass p p' => UMEnv p -> [MonoKind p] -> [MonoKind p] -> UM p ()
unify_kis env orig_xs orig_ys = go orig_xs orig_ys
  where
    go [] [] = return ()
    go (x:xs) (y:ys) = do
      unify_ki env x y
      go xs ys
    go _ _ = surelyApart

uKiVar :: HasPass p p' => UMEnv p -> KiVar p -> MonoKind p -> UM p ()
uKiVar env kv1 ki = do
  let kv1' = umRnKvOccL env kv1
  subst <- getKvSubstEnv
  case lookupVarEnv subst kv1' of
    Just ki' | um_unif env
               -> unify_ki env ki' ki
             | otherwise
               -> unless (ki' `tcEqMonoKind` ki) $ surelyApart
    Nothing -> uUnrefined env kv1' ki 

uUnrefined :: HasPass p p' => UMEnv p -> KiVar p -> MonoKind p -> UM p ()
uUnrefined env kv1 ki2
  | KiVarKi kv2 <- ki2
  = do let kv2' = umRnKvOccR env kv2
       unless (kv1 == kv2' && um_unif env) $ do
         subst <- getKvSubstEnv
         case lookupVarEnv subst kv2 of
           Just ki' | um_unif env -> uUnrefined env kv1 ki'
           _ -> let rhs1 = ki2
                    rhs2 = ki1
                    ki1 = mkKiVarKi kv1
                    b1 = kvBindFlag env kv1 rhs1
                    b2 = kvBindFlag env kv2' rhs2
                in case (b1, b2) of
                     (BindMe, _) -> bindKv env kv1 rhs1
                     (_, BindMe) | um_unif env -> bindKv (umSwapRn env) kv2 rhs2
                     _ | kv1 == kv2' -> return ()
                     _ -> surelyApart

uUnrefined env kv1 ki2 = case kvBindFlag env kv1 ki2 of
  Apart -> surelyApart
  BindMe -> bindKv env kv1 ki2

bindKv :: HasPass p p' => UMEnv p -> KiVar p -> MonoKind p -> UM p ()
bindKv env kv1 ki2 = do
  let free_kvs2 = varsOfMonoKind ki2
  checkRnEnv env free_kvs2
  occurs <- occursCheck env kv1 free_kvs2
  if occurs
    then maybeApart MARInfinite
    else extendKvEnv kv1 ki2

occursCheck :: HasPass p p' => UMEnv p -> KiVar p -> KiVarSet p -> UM p Bool
occursCheck env kv free_kvs
  | um_unif env
  = do subst <- getKvSubstEnv
       return (kv `elemVarSet` niSubstKvSet subst free_kvs)
  | otherwise
  = return False

{- *********************************************************************
*                                                                      *
                Binding decisions
*                                                                      *
********************************************************************* -}

data BindFlag
  = BindMe
  | Apart
  deriving Eq

{- *********************************************************************
*                                                                      *
                Unification monad
*                                                                      *
********************************************************************* -}

data UMEnv p = UMEnv
  { um_unif :: Bool
  , um_inj_tf :: Bool
  , um_rn_envs :: RnEnv2s p
  , um_skols :: (TyVarSet p, KiCoVarSet p, KiVarSet p)
  , um_bind_fun :: BindFuns p
  }

data UMState p = UMState
  { um_tv_env :: TvSubstEnv p p
  , um_kcv_env :: KCvSubstEnv p p
  , um_kv_env :: KvSubstEnv p p }

newtype UM p a = UM' { unUM :: UMState p -> UnifyResultM (UMState p, a) }

pattern UM :: (UMState p -> UnifyResultM (UMState p, a)) -> UM p a
pattern UM m <- UM' m
  where
    UM m = UM' (oneShot m)
{-# COMPLETE UM #-}

instance Functor (UM p) where
  fmap f (UM m) = UM (\s -> fmap (\(s', v) -> (s', f v)) (m s))

instance Applicative (UM p) where
  pure a = UM (\s -> pure (s, a))
  (<*>) = ap

instance Monad (UM p) where
  {-# INLINE (>>=) #-}
  m >>= k = UM (\state -> do (state', v) <- unUM m state
                             unUM (k v) state')

instance MonadFail (UM p) where
  fail _ = UM (\_ -> SurelyApart)

initUM :: SubstEnvs p -> UM p a -> UnifyResultM a
initUM (tv_env, kcv_env, kv_env) um = case unUM um state of
  Unifiable (_, subst) -> Unifiable subst
  MaybeApart r (_, subst) -> MaybeApart r subst
  SurelyApart -> SurelyApart
  where
    state = UMState { um_tv_env = tv_env
                    , um_kcv_env = kcv_env
                    , um_kv_env = kv_env }

tvBindFlag :: UMEnv p -> TyVar p -> Type p -> BindFlag
tvBindFlag env tv rhs
  | tv `elemVarSet` fstOf3 (um_skols env) = Apart
  | otherwise = fstOf3 (um_bind_fun env) tv rhs

kvBindFlag :: UMEnv p -> KiVar p -> MonoKind p -> BindFlag
kvBindFlag  env kv rhs
  | kv `elemVarSet` thdOf3 (um_skols env) = Apart
  | otherwise = thdOf3 (um_bind_fun env) kv rhs

getSubstEnvs :: UM p (SubstEnvs p)
getSubstEnvs = UM $ \state -> Unifiable (state, ( um_tv_env state
                                                , um_kcv_env state
                                                , um_kv_env state ))

getTvSubstEnv :: UM p (TvSubstEnv p p)
getTvSubstEnv = UM $ \state -> Unifiable (state, um_tv_env state)

getKCvSubstEnv :: UM p (KCvSubstEnv p p)
getKCvSubstEnv = UM $ \state -> Unifiable (state, um_kcv_env state)

getKvSubstEnv :: UM p (KvSubstEnv p p)
getKvSubstEnv = UM $ \state -> Unifiable (state, um_kv_env state)

getSubst :: UMEnv p -> UM p (Subst p p)
getSubst env = do
  tv_env <- getTvSubstEnv
  kcv_env <- getKCvSubstEnv
  kv_env <- getKvSubstEnv
  let tv_in_scope = rnInScopeSet (fstOf3 (um_rn_envs env))
      kcv_in_scope = rnInScopeSet (sndOf3 (um_rn_envs env))
      kv_in_scope = rnInScopeSet (thdOf3 (um_rn_envs env))
  return $ Subst { id_env = emptyVarEnv
                 , id_in_scope = emptyInScopeSet
                 , tcv_env = emptyVarEnv
                 , tcv_in_scope = emptyInScopeSet
                 , .. }

extendTvEnv :: TyVar p -> Type p -> UM p ()
extendTvEnv tv ty = UM $ \state ->
  Unifiable (state { um_tv_env = extendVarEnv (um_tv_env state) tv ty }, ())

extendKvEnv :: KiVar p -> MonoKind p -> UM p ()
extendKvEnv kv ki = UM $ \state ->
  Unifiable (state { um_kv_env = extendVarEnv (um_kv_env state) kv ki }, ())

umRnTvBndr2 :: UMEnv p -> TyVar p -> TyVar p -> UMEnv p 
umRnTvBndr2 env v1 v2
  = env { um_rn_envs = rn_env', um_skols = um_skols' }
  where
    (tv_env, kcv_env, kv_env) = um_rn_envs env
    (tv_skols, kcv_skols, kv_skols) = um_skols env
    (tv_env', v') = rnBndr2_var tv_env v1 v2
    tv_skols' = tv_skols `extendVarSet` v'
    rn_env' = (tv_env', kcv_env, kv_env)
    um_skols' = (tv_skols', kcv_skols, kv_skols)

umRnKCvBndr2 :: UMEnv p -> KiCoVar p -> KiCoVar p -> UMEnv p 
umRnKCvBndr2 env v1 v2
  = env { um_rn_envs = rn_env', um_skols = um_skols' }
  where
    (tv_env, kcv_env, kv_env) = um_rn_envs env
    (tv_skols, kcv_skols, kv_skols) = um_skols env
    (kcv_env', v') = rnBndr2_var kcv_env v1 v2
    kcv_skols' = kcv_skols `extendVarSet` v'
    rn_env' = (tv_env, kcv_env', kv_env)
    um_skols' = (tv_skols, kcv_skols', kv_skols)

umRnKvBndr2 :: UMEnv p -> KiVar p -> KiVar p -> UMEnv p 
umRnKvBndr2 env v1 v2
  = env { um_rn_envs = rn_env', um_skols = um_skols' }
  where
    (tv_env, kcv_env, kv_env) = um_rn_envs env
    (tv_skols, kcv_skols, kv_skols) = um_skols env
    (kv_env', v') = rnBndr2_var kv_env v1 v2
    kv_skols' = kv_skols `extendVarSet` v'
    rn_env' = (tv_env, kcv_env, kv_env')
    um_skols' = (tv_skols, kcv_skols, kv_skols')

checkRnEnvT :: UMEnv p -> TyVarSet p -> UM p ()
checkRnEnvT env varset
  | isEmptyVarSet skol_vars = return ()
  | varset `disjointVarSet` skol_vars = return ()
  | otherwise = surelyApart
  where
    skol_vars = fstOf3 (um_skols env)

checkRnEnv :: UMEnv p -> KiVarSet p -> UM p ()
checkRnEnv env varset
  | isEmptyVarSet skol_vars = return ()
  | varset `disjointVarSet` skol_vars = return ()
  | otherwise = surelyApart
  where
    skol_vars = thdOf3 (um_skols env)

umRnKvOccL :: UMEnv p -> KiVar p -> KiVar p
umRnKvOccL env v = rnOccL (thdOf3 $ um_rn_envs env) v

umRnKvOccR :: UMEnv p -> KiVar p -> KiVar p
umRnKvOccR env v = rnOccR (thdOf3 $ um_rn_envs env) v

umRnTvOccL :: UMEnv p -> TyVar p -> TyVar p
umRnTvOccL env v = rnOccL (fstOf3 $ um_rn_envs env) v

umRnTvOccR :: UMEnv p -> TyVar p -> TyVar p
umRnTvOccR env v = rnOccR (fstOf3 $ um_rn_envs env) v

umSwapRn :: UMEnv p -> UMEnv p
umSwapRn env = env { um_rn_envs = ( rnSwap (fstOf3 $ um_rn_envs env)
                                  , rnSwap (sndOf3 $ um_rn_envs env)
                                  , rnSwap (thdOf3 $ um_rn_envs env) )}

maybeApart :: MaybeApartReason -> UM p ()
maybeApart  r = UM (\state -> MaybeApart r (state, ()))

surelyApart :: UM p a
surelyApart  = UM (\_ -> SurelyApart)
