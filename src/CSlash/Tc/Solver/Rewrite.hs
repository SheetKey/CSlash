{-# LANGUAGE BangPatterns #-}

module CSlash.Tc.Solver.Rewrite where

import CSlash.Core.Type.Ppr ( pprTyVar )
import CSlash.Tc.Types ( TcGblEnv(), KiRewriteEnv(..) )

import CSlash.Tc.Types.Constraint
-- import GHC.Core.Predicate
import CSlash.Tc.Utils.TcType
import CSlash.Core.Type
-- import GHC.Tc.Types.Evidence
import CSlash.Core.TyCon
import CSlash.Core.Type.Rep
import CSlash.Core.Kind
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

newtype RewriteM a = RewriteM { runRewriteM :: KiRewriteEnv -> TcS a }

mkRewriteM :: (KiRewriteEnv -> TcS a) -> RewriteM a
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

runRewriteCtEv :: CtKiEvidence -> RewriteM a -> TcS (a, KiRewriterSet)
runRewriteCtEv ev = runRewrite (ctEvLoc ev) (ctEvFlavor ev)

runRewrite :: CtLoc -> CtFlavor -> RewriteM a -> TcS (a, KiRewriterSet)
runRewrite loc flav thing_inside = do
  rewriters_ref <- newTcRef emptyKiRewriterSet
  let fmode = KRE { kre_loc = loc
                 , kre_flavor = flav
                 , kre_rewriters = rewriters_ref }
  res <- runRewriteM thing_inside fmode
  rewriters <- readTcRef rewriters_ref
  return (res, rewriters)

traceRewriteM :: String -> SDoc -> RewriteM ()
traceRewriteM herald doc = liftTcS $ traceTcS herald doc
{-# INLINE traceRewriteM #-}

getRewriteEnv :: RewriteM KiRewriteEnv
getRewriteEnv = mkRewriteM $ \env -> return env

getRewriteEnvField :: (KiRewriteEnv -> a) -> RewriteM a
getRewriteEnvField accessor = mkRewriteM $ \env -> return (accessor env)

getFlavor :: RewriteM CtFlavor
getFlavor = getRewriteEnvField kre_flavor

getLoc :: RewriteM CtLoc
getLoc = getRewriteEnvField kre_loc

bumpDepth :: RewriteM a -> RewriteM a
bumpDepth (RewriteM thing_inside) = mkRewriteM $ \env ->
  let !env' = env { kre_loc = bumpCtLocDepth (kre_loc env) }
  in thing_inside env'

recordRewriter :: CtKiEvidence -> RewriteM ()
recordRewriter (CtKiWanted { ctkev_dest = hole })
  = RewriteM $ \env -> updTcRef (kre_rewriters env) (`addKiRewriter` hole)
recordRewriter other = pprPanic "recordRewriter" (ppr other)

{- *********************************************************************
*                                                                      *
*      Externally callable rewriting functions                         *
*                                                                      *
********************************************************************* -}

rewriteKi :: CtKiEvidence -> AnyMonoKind -> TcS (Reduction, KiRewriterSet)
rewriteKi ev ki = do
  traceTcS "rewriteKi {" (ppr ki)
  result@(redn, _) <- runRewriteCtEv ev (rewrite_one_ki ki)
  traceTcS "rewriteKi }" (ppr $ reductionReducedKind redn)
  return result

rewriteKiForErrors :: CtKiEvidence -> AnyMonoKind -> TcS (Reduction, KiRewriterSet)
rewriteKiForErrors ev ki = do
  traceTcS "rewriteKiForErrors {" (ppr ki)
  result@(redn, rewriters) <- runRewrite (ctEvLoc ev) (ctEvFlavor ev) (rewrite_one_ki ki)
  traceTcS "rewriteKiForErrors }" (ppr $ reductionReducedKind redn)
  return result

{- *********************************************************************
*                                                                      *
*           The main rewriting functions
*                                                                      *
********************************************************************* -}

-- {-# INLINE rewrite_args_kc #-}
-- rewrite_args_kc :: KiCon -> [AnyMonoKind] -> RewriteM Reductions
-- rewrite_args_kc _ = rewrite_args_fast

{-# INLINE rewrite_args_fast #-}
rewrite_args_fast :: [AnyMonoKind] -> RewriteM Reductions
rewrite_args_fast orig_kis = iterate orig_kis
  where
    iterate :: [AnyMonoKind] -> RewriteM Reductions
    iterate (ki:kis) = do
      ReductionKi co xi <- rewrite_one_ki ki
      Reductions cos xis <- iterate kis
      pure $ Reductions (co : cos) (xi : xis)
    iterate [] = pure $ Reductions [] []

rewrite_one_ki :: AnyMonoKind -> RewriteM Reduction

rewrite_one_ki (KiVarKi kv) = rewriteKiVar kv

rewrite_one_ki ki@(BIKi _) = return $ mkReflRednKi ki

rewrite_one_ki KiPredApp {} = panic "rewrite_one_ki Pred"

-- rewrite_one_ki (KiConApp kc kis) = rewrite_ki_con_app kc kis

rewrite_one_ki (FunKi { fk_f = vis, fk_arg = ki1, fk_res = ki2 }) = do
  arg_redn <- rewrite_one_ki ki1
  res_redn <- rewrite_one_ki ki2
  return $ mkFunKiRedn vis arg_redn res_redn

rewrite_reduction :: Reduction -> RewriteM Reduction
rewrite_reduction (ReductionKi co ki) = do
  redn <- bumpDepth $ rewrite_one_ki ki
  return $ co `mkTransRedn` redn

-- rewrite_ki_con_app :: KiCon -> [AnyMonoKind] -> RewriteM Reduction
-- rewrite_ki_con_app kc kis = do
--   redns <- rewrite_args_kc kc kis
--   return $ mkKiConAppRedn kc redns

{- *********************************************************************
*                                                                      *
             Rewriting a kind variable
*                                                                      *
********************************************************************* -}

data RewriteKvResult
  = RKRNotFollowed
  | RKRFollowed !Reduction
 
rewriteKiVar :: AnyKiVar -> RewriteM Reduction
rewriteKiVar kv = do
  mb_yes <- rewrite_kivar1 kv
  case mb_yes of
    RKRFollowed redn -> rewrite_reduction redn
    RKRNotFollowed -> return $ mkReflRednKi $ mkKiVarKi kv

rewrite_kivar1 :: AnyKiVar -> RewriteM RewriteKvResult
rewrite_kivar1 kv = do
  mb_ki <- liftTcS $ handleAnyKv (const (return Nothing)) isFilledMetaKiVar_maybe kv
  case mb_ki of
    Just ki -> do
      traceRewriteM "Following filled kivar"
        (ppr kv <+> equals <+> ppr ki)
      return $ RKRFollowed $ mkReflRednKi ki
    Nothing -> do
      traceRewriteM "Unfilled kivar" (ppr kv)
      f <- getFlavor
      rewrite_kivar2 kv f

rewrite_kivar2 :: AnyKiVar -> CtFlavor -> RewriteM RewriteKvResult
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
            when wrw $ recordRewriter ctev

            let rewriting_co = ctEvKiCoercion ctev
            return $ RKRFollowed $ mkReductionKi rewriting_co rhs_ki
    _ -> return RKRNotFollowed
  where
    can_rewrite :: KiCoCt -> Bool
    can_rewrite ct = kiCoCtFlavor ct `eqCanRewriteF` f
