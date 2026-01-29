{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE PatternSynonyms #-}

module CSlash.Core.Unify where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Name( Name, mkSysTvName, mkSystemVarName )
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

type BindFun = KiVar Tc -> MonoKind Tc -> BindFlag

{- *********************************************************************
*                                                                      *
                Unification
*                                                                      *
********************************************************************* -}

type UnifyResult = UnifyResultM (Subst Tc Tc)

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

tcUnifyKisFG :: BindFun -> [MonoKind Tc] -> [MonoKind Tc] -> UnifyResult
tcUnifyKisFG bind_fn kis1 kis2 = tc_unify_kis_fg bind_fn kis1 kis2

tc_unify_kis_fg :: BindFun -> [MonoKind Tc] -> [MonoKind Tc] -> UnifyResult
tc_unify_kis_fg bind_fn kis1 kis2 = do
  env <- tc_unify_kis bind_fn True False rn_env emptyVarEnv kis1 kis2
  return $ niFixSubst in_scope env
  where
    in_scope = mkInScopeSet $ varsOfMonoKinds kis1 `unionVarSet` varsOfMonoKinds kis2
    rn_env = mkRnEnv2 in_scope

tc_unify_kis
  :: BindFun
  -> Bool
  -> Bool
  -> RnEnv2 (KiVar Tc)
  -> KvSubstEnv Tc Tc
  -> [MonoKind Tc]
  -> [MonoKind Tc]
  -> UnifyResultM (KvSubstEnv Tc Tc)
tc_unify_kis bind_fn unif inj_check rn_env kv_env kis1 kis2 = initUM kv_env $ do
  unify_kis env kis1 kis2
  getKvSubstEnv
  where
    env = UMEnv { um_bind_fun = bind_fn
                , um_skols = emptyVarSet
                , um_unif = unif
                , um_inj_tf = inj_check
                , um_rn_env = rn_env }

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

    range_kvs = case fvVarAcc range_fvs of
                  (kvs, _) -> kvs

    not_fixpoint = any in_domain range_kvs
    in_domain kv = kv `elemVarEnv` kenv

    free_kvs = filterOut in_domain range_kvs

    subst = foldl' add_free_kv (mkKvSubst in_scope kenv) free_kvs

    add_free_kv subst kv = extendKvSubst subst kv (mkKiVarKi kv)

niSubstKvSet :: KvSubstEnv Tc Tc -> KiVarSet Tc -> KiVarSet Tc
niSubstKvSet subst kvs = nonDetStrictFoldUniqSet (unionVarSet . get) emptyVarSet kvs
  where
    get kv
      | Just ki <- lookupVarEnv subst kv
      = niSubstKvSet subst (varsOfMonoKind ki)
      | otherwise
      = unitVarSet kv

{- *********************************************************************
*                                                                      *
                unify_ty: the main workhorse
*                                                                      *
********************************************************************* -}

unify_ki :: UMEnv -> MonoKind Tc -> MonoKind Tc -> UM ()

unify_ki _ (BIKi k1) (BIKi k2)
  | k1 == k2
  = return ()

unify_ki env (KiVarKi kv1) ki2 = uVar env kv1 ki2

unify_ki env ki1 (KiVarKi kv2) = uVar (umSwapRn env) kv2 ki1

unify_ki env ki1 ki2
  | KiPredApp kc1 _ _ <- ki1
  , KiPredApp kc2 _ _ <- ki2
  --, kc1 == kc2
  = panic "unify_kis env kis1 kis2"

  | FunKi {} <- ki1
  , FunKi {} <- ki2
  = maybeApart MARKindVsConstraint

unify_ki _ _ _ = surelyApart

unify_kis :: UMEnv -> [MonoKind Tc] -> [MonoKind Tc] -> UM ()
unify_kis env orig_xs orig_ys = go orig_xs orig_ys
  where
    go [] [] = return ()
    go (x:xs) (y:ys) = do
      unify_ki env x y
      go xs ys
    go _ _ = surelyApart

uVar :: UMEnv -> KiVar Tc -> MonoKind Tc -> UM ()
uVar env kv1 ki = do
  let kv1' = umRnOccL env kv1
  subst <- getKvSubstEnv
  case lookupVarEnv subst kv1' of
    Just ki' | um_unif env
               -> unify_ki env ki' ki
             | otherwise
               -> unless (ki' `tcEqMonoKind` ki) $ surelyApart
    Nothing -> uUnrefined env kv1' ki 

uUnrefined :: UMEnv -> KiVar Tc -> MonoKind Tc -> UM ()
uUnrefined env kv1 ki2
  | KiVarKi kv2 <- ki2
  = do let kv2' = umRnOccR env kv2
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

bindKv :: UMEnv -> KiVar Tc -> MonoKind Tc -> UM ()
bindKv env kv1 ki2 = do
  let free_kvs2 = varsOfMonoKind ki2
  checkRnEnv env free_kvs2
  occurs <- occursCheck env kv1 free_kvs2
  if occurs
    then maybeApart MARInfinite
    else extendKvEnv kv1 ki2

occursCheck :: UMEnv -> KiVar Tc -> KiVarSet Tc -> UM Bool
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

data UMEnv = UMEnv
  { um_unif :: Bool
  , um_inj_tf :: Bool
  , um_rn_env :: RnEnv2 (KiVar Tc)
  , um_skols :: KiVarSet Tc
  , um_bind_fun :: BindFun
  }

data UMState = UMState { um_kv_env :: KvSubstEnv Tc Tc }

newtype UM a = UM' { unUM :: UMState -> UnifyResultM (UMState, a) }

pattern UM :: (UMState -> UnifyResultM (UMState, a)) -> UM a
pattern UM m <- UM' m
  where
    UM m = UM' (oneShot m)
{-# COMPLETE UM #-}

instance Functor UM where
  fmap f (UM m) = UM (\s -> fmap (\(s', v) -> (s', f v)) (m s))

instance Applicative UM where
  pure a = UM (\s -> pure (s, a))
  (<*>) = ap

instance Monad UM where
  {-# INLINE (>>=) #-}
  m >>= k = UM (\state -> do (state', v) <- unUM m state
                             unUM (k v) state')

instance MonadFail UM where
  fail _ = UM (\_ -> SurelyApart)

initUM :: KvSubstEnv Tc Tc -> UM a -> UnifyResultM a
initUM subst_env um = case unUM um state of
  Unifiable (_, subst) -> Unifiable subst
  MaybeApart r (_, subst) -> MaybeApart r subst
  SurelyApart -> SurelyApart
  where
    state = UMState { um_kv_env = subst_env }

kvBindFlag :: UMEnv -> KiVar Tc -> MonoKind Tc -> BindFlag
kvBindFlag  env kv rhs
  | kv `elemVarSet` um_skols env = Apart
  | otherwise = um_bind_fun env kv rhs

getKvSubstEnv :: UM (KvSubstEnv Tc Tc)
getKvSubstEnv = UM $ \state -> Unifiable (state, um_kv_env state)

extendKvEnv :: KiVar Tc -> MonoKind Tc -> UM ()
extendKvEnv kv ki = UM $ \state ->
  Unifiable (state { um_kv_env = extendVarEnv (um_kv_env state) kv ki }, ())

checkRnEnv :: UMEnv -> KiVarSet Tc -> UM ()
checkRnEnv env varset
  | isEmptyVarSet skol_vars = return ()
  | varset `disjointVarSet` skol_vars = return ()
  | otherwise = surelyApart
  where
    skol_vars = um_skols env

umRnOccL :: UMEnv -> KiVar Tc -> KiVar Tc
umRnOccL env v = rnOccL (um_rn_env env) v

umRnOccR :: UMEnv -> KiVar Tc -> KiVar Tc
umRnOccR env v = rnOccR (um_rn_env env) v

umSwapRn :: UMEnv -> UMEnv
umSwapRn env = env { um_rn_env = rnSwap (um_rn_env env) }

maybeApart :: MaybeApartReason -> UM ()
maybeApart  r = UM (\state -> MaybeApart r (state, ()))

surelyApart :: UM a
surelyApart  = UM (\_ -> SurelyApart)
