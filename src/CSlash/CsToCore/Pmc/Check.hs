{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.CsToCore.Pmc.Check where

import Prelude hiding ((<>))

import CSlash.Builtin.Names ( hasKey{-, considerAccessibleIdKey-}, trueDataConKey )
import CSlash.CsToCore.Monad ( DsM )
import CSlash.CsToCore.Pmc.Types
import CSlash.CsToCore.Pmc.Utils
import CSlash.CsToCore.Pmc.Solver
import CSlash.Driver.DynFlags
import CSlash.Utils.Outputable
import CSlash.Tc.Utils.TcType (tyCoVarPred)
import CSlash.Data.OrdList
import CSlash.Data.Bag

import qualified Data.Semigroup as Semi
import Data.List.NonEmpty ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NE
import Data.Coerce
import CSlash.Types.Var
import CSlash.Core
import CSlash.Core.Utils

newtype CheckAction a = CA { unCA :: Nablas -> DsM (CheckResult a) }
  deriving Functor

matchSucceeded :: CheckAction RedSets
matchSucceeded = CA $ \inc ->
  pure CheckResult { cr_ret = emptyRedSets { rs_cov = inc }
                   , cr_uncov = mempty
                   , cr_approx = Precise }

topToBottom
  :: ((Nablas -> (Precision, Nablas)) -> top -> bot -> (Precision, ret))
  -> CheckAction top
  -> CheckAction bot
  -> CheckAction ret
topToBottom f (CA top) (CA bot) = CA $ \inc -> do
  t <- top inc
  b <- bot (cr_uncov t)
  limit <- maxPmCheckModels <$> getDynFlags
  let throttler cov = throttle limit inc cov
  let (prec', ret) = f throttler (cr_ret t) (cr_ret b)
  pure CheckResult { cr_ret = ret
                   , cr_uncov = cr_uncov b
                   , cr_approx = prec' Semi.<> cr_approx t Semi.<> cr_approx b }

leftToRight
  :: (RedSets -> right -> ret)
  -> CheckAction RedSets
  -> CheckAction right
  -> CheckAction ret
leftToRight f (CA left) (CA right) = CA $ \inc -> do
  l <- left inc
  r <- right (rs_cov (cr_ret l))
  limit <- maxPmCheckModels <$> getDynFlags
  let uncov = cr_uncov l Semi.<> cr_uncov r
  let (prec', uncov') = throttle limit inc uncov
  pure CheckResult { cr_ret = f (cr_ret l) (cr_ret r)
                   , cr_uncov = uncov'
                   , cr_approx = prec' Semi.<> cr_approx l Semi.<> cr_approx r }

throttle :: Int -> Nablas -> Nablas -> (Precision, Nablas)
throttle limit old@(MkNablas old_ds) new@(MkNablas new_ds)
  | length new_ds > max limit (length old_ds) = (Approximate, old)
  | otherwise = (Precise, new)

checkAlternatives
  :: (grdtree -> CheckAction anntree)
  -> NonEmpty grdtree
  -> CheckAction (NonEmpty anntree)
checkAlternatives act (t :| []) = (:| []) <$> act t
checkAlternatives act (t1 :| (t2:ts)) =
  topToBottom (no_throttling (NE.<|)) (act t1) (checkAlternatives act (t2:|ts))
  where
    no_throttling f _ t b = (Precise, f t b)

emptyRedSets :: RedSets
emptyRedSets = RedSets mempty mempty 

checkGrd :: PmGrd -> CheckAction RedSets
checkGrd grd = CA $ \inc -> case grd of
  PmLet x e -> do
    matched <- addPhiCtNablas inc (PhiCoreCt x e)
    tracePm "check:Let" (ppr x <+> char '=' <+> ppr e)
    pure CheckResult { cr_ret = emptyRedSets { rs_cov = matched }
                     , cr_uncov = mempty
                     , cr_approx = Precise }
  -- TODO: all things in guards should be unrestricted(affine?)!
  -- This ensure we can allow guards to shortcut when checking bools
  PmCon x con tvs args -> do
    !div <- addPhiCtNablas inc (PhiBotCt x)
    !matched <- addPhiCtNablas inc (PhiConCt x con tvs args)
    !uncov <- addPhiCtNablas inc (PhiNotConCt x con)
    tracePm "check:Con"
      $ vcat [ ppr grd
             , ppr inc
             , hang (text "div") 2 (ppr div)
             , hang (text "matched") 2 (ppr matched)
             , hang (text "uncov") 2 (ppr uncov)
             ]
    pure CheckResult { cr_ret = emptyRedSets { rs_cov = matched, rs_div = div }
                     , cr_uncov = uncov
                     , cr_approx = Precise }

checkGrdDag :: GrdDag -> CheckAction RedSets
checkGrdDag (GdOne g) = checkGrd g
checkGrdDag GdEnd = matchSucceeded
checkGrdDag (GdSeq dl dr) = leftToRight merge (checkGrdDag dl) (checkGrdDag dr)
  where
    merge ri_l ri_r =
      RedSets { rs_cov = rs_cov ri_r
              , rs_div = rs_div ri_l Semi.<> rs_div ri_r }
checkGrdDag (GdAlt dt db) = topToBottom merge (checkGrdDag dt) (checkGrdDag db)
  where
    merge throttler ri_t ri_b =
      let (prec, cov) = throttler (rs_cov ri_t Semi.<> rs_cov ri_b)
      in (prec, RedSets { rs_cov = cov
                        , rs_div = rs_div ri_t Semi.<> rs_div ri_b })

checkMatchGroup :: PmMatchGroup Pre -> CheckAction (PmMatchGroup Post)
checkMatchGroup (PmMatchGroup matches)
  = PmMatchGroup <$> checkAlternatives checkMatch matches

checkMatch :: PmMatch Pre -> CheckAction (PmMatch Post)
checkMatch (PmMatch { pm_pats = grds, pm_grhss = grhss })
  = leftToRight PmMatch (checkGrdDag grds) (checkGRHSs grhss)

checkGRHSs :: PmGRHSs Pre -> CheckAction (PmGRHSs Post)
checkGRHSs (PmGRHSs { pgs_grhss = grhss })
  = PmGRHSs <$> checkAlternatives checkGRHS grhss

checkGRHS :: PmGRHS Pre -> CheckAction (PmGRHS Post)
checkGRHS (PmGRHS { pg_grds = grds, pg_rhs = rhs_info })
  = flip PmGRHS rhs_info <$> checkGrdDag grds
