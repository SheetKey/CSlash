{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Tc.Solver.Rewrite where

import CSlash.Cs.Pass

import CSlash.Core.Type.Ppr ( pprTyVar )
import CSlash.Tc.Types ( TcGblEnv(), RewriteEnv(..) )

import CSlash.Tc.Types.Constraint
-- import GHC.Core.Predicate
import CSlash.Tc.Utils.TcType
import CSlash.Core.Type
-- import GHC.Tc.Types.Evidence
import CSlash.Core.TyCon
import CSlash.Core.Type.Rep
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs
-- import GHC.Core.Coercion
import CSlash.Core.Reduction
import CSlash.Types.Unique.FM
import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Driver.DynFlags
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Tc.Solver.Monad as TcS

import CSlash.Utils.Misc
import CSlash.Data.Maybe
import GHC.Exts (oneShot)
import Control.Monad
import Control.Applicative (liftA3)
-- import GHC.Builtin.Types (tYPETyCon)
import Data.List ( find )
import CSlash.Data.List.Infinite (Infinite)
import CSlash.Data.Bag( listToBag )
import qualified CSlash.Data.List.Infinite as Inf

{- *********************************************************************
*                                                                      *
*                RewriteEnv & RewriteM
*             The rewriting environment & monad
*                                                                      *
********************************************************************* -}

newtype RewriteM a = RewriteM { runRewriteM :: RewriteEnv -> TcS a }

mkRewriteM :: (RewriteEnv -> TcS a) -> RewriteM a
mkRewriteM f = RewriteM (oneShot f)
{-# INLINE mkRewriteM #-}

instance Monad RewriteM where
  m >>= k = mkRewriteM $ \env -> do
    a <- runRewriteM m env
    runRewriteM (k a) env

instance Applicative RewriteM where
  pure x = mkRewriteM $ \_ -> pure x
  (<*>) = ap

instance Functor RewriteM where
  fmap f (RewriteM x) = mkRewriteM $ \env -> fmap f (x env)

instance HasDynFlags RewriteM where
  getDynFlags = liftTcS getDynFlags

liftTcS :: TcS a -> RewriteM a
liftTcS thing_inside = mkRewriteM $ \_ -> thing_inside

runRewriteTyCtEv  :: CtTyEvidence -> RewriteM a -> TcS (a, TyRewriterSet, KiRewriterSet)
runRewriteTyCtEv ev = runRewriteTy (ctEvLoc ev) (ctEvFlavor ev)

runRewriteTy :: CtLoc -> CtFlavor -> RewriteM a -> TcS (a, TyRewriterSet, KiRewriterSet)
runRewriteTy loc flav thing_inside = do
  ty_rewriters_ref <- newTcRef emptyTyRewriterSet
  ki_rewriters_ref <- newTcRef emptyKiRewriterSet
  let fmode = RE { re_loc = loc
                 , re_flavor = flav
                 , re_ty_rewriters = ty_rewriters_ref
                 , re_ki_rewriters = ki_rewriters_ref }
  res <- runRewriteM thing_inside fmode
  ty_rewriters <- readTcRef ty_rewriters_ref
  ki_rewriters <- readTcRef ki_rewriters_ref
  return (res, ty_rewriters, ki_rewriters)

runRewriteKiCtEv :: CtKiEvidence -> RewriteM a -> TcS (a, KiRewriterSet)
runRewriteKiCtEv ev = runRewriteKi (ctEvLoc ev) (ctEvFlavor ev)

runRewriteKi :: CtLoc -> CtFlavor -> RewriteM a -> TcS (a, KiRewriterSet)
runRewriteKi loc flav thing_inside = do
  rewriters_ref <- newTcRef emptyKiRewriterSet
  ty_rewriters_ref <- newTcRef emptyTyRewriterSet
  let fmode = RE { re_loc = loc
                 , re_flavor = flav
                 , re_ty_rewriters = ty_rewriters_ref
                 , re_ki_rewriters = rewriters_ref }
  res <- runRewriteM thing_inside fmode
  rewriters <- readTcRef rewriters_ref
  ty_rewriters <- readTcRef ty_rewriters_ref
  unless (isEmptyTyRewriterSet ty_rewriters) $
    pprPanic "runRewriteKi ty_rewriters" (ppr ty_rewriters)
  return (res, rewriters)

traceRewriteM :: String -> SDoc -> RewriteM ()
traceRewriteM herald doc = liftTcS $ traceTcS herald doc
{-# INLINE traceRewriteM #-}

getRewriteEnv :: RewriteM RewriteEnv
getRewriteEnv = mkRewriteM $ \env -> return env

getRewriteEnvField :: (RewriteEnv -> a) -> RewriteM a
getRewriteEnvField accessor = mkRewriteM $ \env -> return (accessor env)

getFlavor :: RewriteM CtFlavor
getFlavor = getRewriteEnvField re_flavor

getLoc :: RewriteM CtLoc
getLoc = getRewriteEnvField re_loc

bumpDepth :: RewriteM a -> RewriteM a
bumpDepth (RewriteM thing_inside) = mkRewriteM $ \env ->
  let !env' = env { re_loc = bumpCtLocDepth (re_loc env) }
  in thing_inside env'

recordTyRewriter :: CtTyEvidence -> RewriteM ()
recordTyRewriter (CtTyWanted { cttev_dest = hole })
  = RewriteM $ \env -> updTcRef (re_ty_rewriters env) (`addTyRewriter` hole)
recordTyRewriter other = pprPanic "recordTyRewriter" (ppr other)

recordKiRewriter :: CtKiEvidence -> RewriteM ()
recordKiRewriter (CtKiWanted { ctkev_dest = hole })
  = RewriteM $ \env -> updTcRef (re_ki_rewriters env) (`addKiRewriter` hole)
recordKiRewriter other = pprPanic "recordKiRewriter" (ppr other)

{- *********************************************************************
*                                                                      *
*      Externally callable rewriting functions                         *
*                                                                      *
********************************************************************* -}

rewriteTy :: CtTyEvidence -> Type Tc -> TcS (TyReduction, TyRewriterSet, KiRewriterSet)
rewriteTy ev ty = do
  traceTcS "rewrite {" (ppr ty)
  result@(redn, _, _) <- runRewriteTyCtEv ev (rewrite_one_ty ty)
  traceTcS "rewrite }" (ppr $ reductionReducedType redn)
  return result

rewriteKi :: CtKiEvidence -> MonoKind Tc -> TcS (KiReduction, KiRewriterSet)
rewriteKi ev ki = do
  traceTcS "rewriteKi {" (ppr ki)
  result@(redn, _) <- runRewriteKiCtEv ev (rewrite_one_ki ki)
  traceTcS "rewriteKi }" (ppr $ reductionReducedKind redn)
  return result

rewriteTyForErrors :: CtTyEvidence -> Type Tc -> TcS (TyReduction, TyRewriterSet, KiRewriterSet)
rewriteTyForErrors ev ty = do
  traceTcS "rewriteTyForErrors {" (ppr ty)
  result@(redn, ty_rewriters, ki_rewriters)
    <- runRewriteTy (ctEvLoc ev) (ctEvFlavor ev) (rewrite_one_ty ty)
  traceTcS "rewriteTyForErrors }" (ppr $ reductionReducedType redn)
  return result

rewriteKiForErrors :: CtKiEvidence -> MonoKind Tc -> TcS (KiReduction, KiRewriterSet)
rewriteKiForErrors ev ki = do
  traceTcS "rewriteKiForErrors {" (ppr ki)
  result@(redn, rewriters) <- runRewriteKi (ctEvLoc ev) (ctEvFlavor ev) (rewrite_one_ki ki)
  traceTcS "rewriteKiForErrors }" (ppr $ reductionReducedKind redn)
  return result

{- *********************************************************************
*                                                                      *
*           The main rewriting functions
*                                                                      *
********************************************************************* -}

rewrite_one_ty :: Type Tc -> RewriteM TyReduction

rewrite_one_ty ty
  | Just ty' <- rewriterView ty
  = rewrite_one_ty ty'

rewrite_one_ty (TyVarTy tv) = rewriteTyVar tv

rewrite_one_ty (AppTy ty1 ty2) = rewrite_app_tys ty1 [ty2]

rewrite_one_ty (TyConApp tc tys) = rewrite_ty_con_app tc tys

rewrite_one_ty (FunTy ki ty1 ty2) = do
  arg_redn <- rewrite_one_ty ty1
  res_redn <- rewrite_one_ty ty2

  let arg_ki = typeMonoKind (reductionReducedType arg_redn)
      res_ki = typeMonoKind (reductionReducedType res_redn)

  (ki_redn, arg_ki_redn, res_ki_redn) <- liftA3 (,,) (rewrite_one_ki ki)
                                                     (rewrite_one_ki arg_ki)
                                                     (rewrite_one_ki res_ki)
  let arg_ki_co = reductionKindCoercion arg_ki_redn
      casted_arg_redn = mkCoherenceRightRedn arg_redn arg_ki_co

      res_ki_co = reductionKindCoercion res_ki_redn
      casted_res_redn = mkCoherenceRightRedn res_redn res_ki_co

  return $ mkFunTyRedn ki_redn casted_arg_redn casted_res_redn

rewrite_one_ty ty@(ForAllTy {}) = do
  let (bndrs, rho) = tcSplitForAllTyVarBinders ty
  redn <- rewrite_one_ty rho
  return $ mkHomoForAllRedn bndrs redn

rewrite_one_ty (CastTy ty g) = do
  redn <- rewrite_one_ty ty
  g' <- rewrite_kco g
  return $ mkCastRedn1 ty g' redn

rewrite_one_ty (KindCoercion kco) = do
  co' <- rewrite_kco kco
  return $ mkReflKiCoRedn co'

rewrite_one_ty (Embed mki) = do
  redn <- rewrite_one_ki mki
  return $ embedKiRedn redn

rewrite_one_ty other = pprPanic "rewrite_one_ty other" (ppr other)

rewrite_kco :: KindCoercion Tc -> RewriteM (KindCoercion Tc)
rewrite_kco co = liftTcS $ zonkKiCo co

rewrite_app_tys :: Type Tc -> [Type Tc] -> RewriteM TyReduction
rewrite_app_tys (AppTy ty1 ty2) tys = rewrite_app_tys ty1 (ty2:tys)
rewrite_app_tys fun_ty arg_tys = do
  redn <- rewrite_one_ty fun_ty
  rewrite_app_ty_args redn arg_tys

rewrite_app_ty_args :: TyReduction -> [Type Tc] -> RewriteM TyReduction
rewrite_app_ty_args redn [] = return redn
rewrite_app_ty_args fun_redn@(TyReduction fun_co fun_xi) arg_tys = do
  het_redn <- case tcSplitTyConApp_maybe fun_xi of
    Just (tc, xis) -> do
      ArgsReductions (TyReductions arg_cos arg_xis) kind_co
        <- rewrite_vector (typeKind fun_xi) arg_tys

      let app_xi = mkTyConApp tc (xis ++ arg_xis)
          app_co = mkAppCos fun_co arg_cos

      return $ mkHetTyReduction (mkTyReduction app_co app_xi) kind_co

    Nothing -> do
      ArgsReductions redns kind_co
        <- rewrite_vector (typeKind fun_xi) arg_tys

      return $ mkHetTyReduction (mkAppRedns fun_redn redns) kind_co

  return $ homogeniseHetTyRedn het_redn

rewrite_ty_con_app :: TyCon Tc -> [Type Tc] -> RewriteM TyReduction
rewrite_ty_con_app tc tys = do
  ArgsReductions redns kind_co <- rewrite_args_tc tc tys
  let tyconapp_redn = mkHetTyReduction (mkTyConAppRedn tc redns) kind_co
  return $ homogeniseHetTyRedn tyconapp_redn

{-# INLINE rewrite_args_tc #-}
rewrite_args_tc :: TyCon Tc -> [Type Tc] -> RewriteM ArgsReductions
rewrite_args_tc tc = case tyConDetails tc of
  TcTyCon { tcTyConKind = ki } -> rewrite_vector ki
  other -> rewrite_vector (tyConKind other)

rewrite_vector :: Kind p -> [Type Tc] -> RewriteM ArgsReductions
rewrite_vector ki tys = 
  rewrite_args bndrs any_named_bndrs inner_ki fvs tys
  where
    (bndrs, inner_ki, any_named_bndrs) = split_pi_kis' ki
    fvs = varsOfKind ki

{-# INLINE rewrite_args #-}
rewrite_args
  :: [PiKiBinder p]
  -> Bool
  -> MonoKind p
  -> KiVarSet p
  -> [Type Tc]
  -> RewriteM ArgsReductions
rewrite_args orig_binders any_named_bndrs orig_inner_ki orig_fvs orig_tys
  = if any_named_bndrs
    then rewrite_args_slow orig_binders orig_inner_ki orig_fvs orig_tys
    else rewrite_args_fast orig_tys

{-# INLINE rewrite_args_fast #-}
rewrite_args_fast :: [Type Tc] -> RewriteM ArgsReductions
rewrite_args_fast orig_tys = fmap finish (iterate orig_tys)
  where
    iterate :: [Type Tc] -> RewriteM TyReductions
    iterate (ty : tys) = do
      TyReduction co xi <- rewrite_one_ty ty
      TyReductions cos xis <- iterate tys
      pure $ TyReductions (co:cos) (xi:xis)
    iterate [] = pure $ TyReductions [] []

    {-# INLINE finish #-}
    finish :: TyReductions -> ArgsReductions
    finish redns = ArgsReductions redns Nothing

{-# INLINE rewrite_args_slow #-}
rewrite_args_slow
  :: [PiKiBinder p]
  -> MonoKind p
  -> KiVarSet p
  -> [Type Tc]
  -> RewriteM ArgsReductions
rewrite_args_slow binders inner_ki fvs tys = do
  rewritten_args <- mapM rewrite_one_ty tys
  return $ simplifyArgsWorker binders inner_ki fvs rewritten_args
  
rewrite_one_ki :: MonoKind Tc -> RewriteM KiReduction

rewrite_one_ki (KiVarKi kv) = rewriteKiVar kv

rewrite_one_ki ki@(BIKi _) = return $ mkReflRednKi ki

rewrite_one_ki KiPredApp {} = panic "rewrite_one_ki Pred"

-- rewrite_one_ki (KiConApp kc kis) = rewrite_ki_con_app kc kis

rewrite_one_ki (FunKi { fk_f = vis, fk_arg = ki1, fk_res = ki2 }) = do
  arg_redn <- rewrite_one_ki ki1
  res_redn <- rewrite_one_ki ki2
  return $ mkFunKiRedn vis arg_redn res_redn

rewrite_reduction :: KiReduction -> RewriteM KiReduction
rewrite_reduction (KiReduction co ki) = do
  redn <- bumpDepth $ rewrite_one_ki ki
  return $ co `mkTransRedn` redn

rewrite_ty_reduction :: TyReduction -> RewriteM TyReduction
rewrite_ty_reduction (TyReduction co xi) = do
  redn <- bumpDepth $ rewrite_one_ty xi
  return $ co `mkTransTyRedn` redn

-- rewrite_ki_con_app :: KiCon -> [AnyMonoKind] -> RewriteM Reduction
-- rewrite_ki_con_app kc kis = do
--   redns <- rewrite_args_kc kc kis
--   return $ mkKiConAppRedn kc redns

{- *********************************************************************
*                                                                      *
             Rewriting a type variable
*                                                                      *
********************************************************************* -}

data RewriteVResult redn
  = RVRNotFollowed
  | RVRFollowed !redn
 
type RewriteTvResult = RewriteVResult TyReduction

rewriteTyVar :: TyVar Tc  -> RewriteM TyReduction
rewriteTyVar tv = do
  mb_yes <- rewrite_tyvar1 tv
  case mb_yes of
    RVRFollowed redn -> rewrite_ty_reduction redn
    RVRNotFollowed -> do
      tv' <- liftTcS $ updateVarKindM zonkTcMonoKind tv
      let ty' = mkTyVarTy tv'
      return $ mkReflRednTy ty'

rewrite_tyvar1 :: TyVar Tc -> RewriteM RewriteTvResult
rewrite_tyvar1 tv = do
  mb_ty <- liftTcS $ isFilledMetaTyVar_maybe tv
  case mb_ty of
    Just ty -> do traceRewriteM "Following filled tyvar"
                    (ppr tv <+> equals <+> ppr ty)
                  return $ RVRFollowed $ mkReflRednTy ty

    Nothing -> do traceRewriteM "Unfilled tyvar" (pprTyVar tv)
                  f <- getFlavor
                  rewrite_tyvar2 tv f

rewrite_tyvar2 :: TyVar Tc -> CtFlavor -> RewriteM RewriteTvResult
rewrite_tyvar2 tv f = do
  ieqs <- liftTcS $ getInertTyEqs
  case lookupDVarEnv ieqs tv of
    Just equal_ct_list
      | Just ct <- find can_rewrite equal_ct_list
      , TyEqCt { teq_ev = ctev, teq_lhs = TyVarLHS tv, teq_rhs = rhs_ty } <- ct
        -> do let wrw = isWanted ctev
              traceRewriteM "Following inert tyvar"
                $ vcat [ ppr tv <+> equals <+> ppr rhs_ty
                       , ppr ctev
                       , text "wanted_rewrite_wanted:" <+> ppr wrw ]
              when wrw $ recordTyRewriter ctev

              let rewriting_co = ctEvTyCoercion ctev
              return $ RVRFollowed $ mkTyReduction rewriting_co rhs_ty
    _ -> return RVRNotFollowed
  where
    can_rewrite :: TyEqCt -> Bool
    can_rewrite ct = tyEqCtFlavor ct `eqCanRewriteF` f

{- *********************************************************************
*                                                                      *
             Rewriting a kind variable
*                                                                      *
********************************************************************* -}

type RewriteKvResult = RewriteVResult KiReduction
 
rewriteKiVar :: KiVar Tc -> RewriteM KiReduction
rewriteKiVar kv = do
  mb_yes <- rewrite_kivar1 kv
  case mb_yes of
    RVRFollowed redn -> rewrite_reduction redn
    RVRNotFollowed -> return $ mkReflRednKi $ mkKiVarKi kv

rewrite_kivar1 :: KiVar Tc -> RewriteM RewriteKvResult
rewrite_kivar1 kv = do
  mb_ki <- liftTcS $ isFilledMetaKiVar_maybe kv
  case mb_ki of
    Just ki -> do
      traceRewriteM "Following filled kivar"
        (ppr kv <+> equals <+> ppr ki)
      return $ RVRFollowed $ mkReflRednKi ki
    Nothing -> do
      traceRewriteM "Unfilled kivar" (ppr kv)
      f <- getFlavor
      rewrite_kivar2 kv f

rewrite_kivar2 :: KiVar Tc -> CtFlavor -> RewriteM RewriteKvResult
rewrite_kivar2 kv f = do
  ieqs <- liftTcS $ getInertKiCos
  case lookupDVarEnv ieqs kv of
    Just equal_ct_list
      | Just ct <- find can_rewrite equal_ct_list
      , KiCoCt { kc_ev = ctev, kc_lhs = KiVarLHS kv, kc_rhs = rhs_ki } <- ct
      -> do let wrw = isWanted ctev
            traceRewriteM "Following inert kivar"
              $ vcat [ ppr kv <+> equals <+> ppr rhs_ki
                     , ppr ctev
                     , text "wanted_rewrite_wanted:" <+> ppr wrw ]
            when wrw $ recordKiRewriter ctev

            let rewriting_co = ctEvKiCoercion ctev
            return $ RVRFollowed $ mkKiReduction rewriting_co rhs_ki
    _ -> return RVRNotFollowed
  where
    can_rewrite :: KiCoCt -> Bool
    can_rewrite ct = kiCoCtFlavor ct `eqCanRewriteF` f

--------------------------------------
-- Utilities

split_pi_kis' :: Kind p -> ([PiKiBinder p], MonoKind p, Bool)
split_pi_kis' ki = split ki
  where
    split (ForAllKi b res) = let !(bs, ki, _) = split res
                             in (Named b : bs, ki, True)
    split (Mono ki) = split_mono ki

    split_mono (FunKi af arg res) = let !(bs, ki, named) = split_mono res
                                    in (Anon arg af : bs, ki, named)
    split_mono ki = ([], ki, False)
{-# INLINE split_pi_kis' #-}
