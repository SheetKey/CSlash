{-# LANGUAGE GADTs #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE LambdaCase #-}

module CSlash.CsToCore.Pmc where

import CSlash.CsToCore.Errors.Types
import CSlash.CsToCore.Pmc.Types
import CSlash.CsToCore.Pmc.Utils
import CSlash.CsToCore.Pmc.Desugar
import CSlash.CsToCore.Pmc.Check
import CSlash.CsToCore.Pmc.Solver
import CSlash.Types.Basic (Origin(..))
import CSlash.Core
import CSlash.Driver.DynFlags
import CSlash.Cs
import CSlash.Types.Var.Id
import CSlash.Types.SrcLoc
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
-- import CSlash.Types.Var (Var (..))
import CSlash.Types.Var.Id.Info
-- import CSlash.Tc.Utils.TcType (evVarPred)
import {-# SOURCE #-} CSlash.CsToCore.Expr (dsLExpr)
import CSlash.CsToCore.Monad
import CSlash.Data.Bag
import CSlash.Data.OrdList

import Control.Monad (when, unless, forM_)
import qualified Data.Semigroup as Semi
import Data.List.NonEmpty ( NonEmpty(..) )
import qualified Data.List.NonEmpty as NE
import Data.Coerce
import CSlash.Tc.Utils.Monad

getLdiNablas :: DsM Nablas
getLdiNablas = do
  nablas <- getPmNablas
  isInhabited nablas >>= \case
    True -> pure nablas
    False -> pure initNablas

noCheckDs :: DsM a -> DsM a
noCheckDs = updTopFlags (\dflags -> foldl' wopt_unset dflags allPmCheckWarnings)

pmcPatBind :: DsMatchContext -> Id Zk -> Pat Zk -> DsM Nablas
pmcPatBind = panic "pmcPatBind"

pmcMatches
  :: Origin
  -> DsMatchContext
  -> [Id Zk]
  -> [LMatch Zk (LCsExpr Zk)]
  -> DsM [(Nablas, NonEmpty Nablas)]
pmcMatches origin ctxt vars matches = {-# SCC "pmcMatches" #-} do
  !missing <- getLdiNablas
  tracePm "pmcMatches {"
    $ hang (vcat [ ppr origin, ppr ctxt, ppr vars, text "Matches:" ])
    2 ((ppr matches) $$ (text "missing:" <+> ppr missing))

  case NE.nonEmpty matches of
    Nothing -> panic "unreachable"
    Just matches -> do
      matches <- {-# SCC "desugarMatches" #-}
                 noCheckDs $ desugarMatches vars matches
      tracePm "desugared matches" (ppr matches)
      result <- {-# SCC "checkMatchGroup" #-}
                unCA (checkMatchGroup matches) missing
      tracePm "}: " (ppr (cr_uncov result))
      unless False -- TODO: do notation stuff
        ({-# SCC "formatReportWarnings" #-}
          formatReportWarnings ReportMatchGroup ctxt vars result)
      return (NE.toList (ldiMatchGroup (cr_ret result)))

ldiMatchGroup :: PmMatchGroup Post -> NonEmpty (Nablas, NonEmpty Nablas)
ldiMatchGroup (PmMatchGroup matches) = ldiMatch <$> matches

ldiMatch :: PmMatch Post -> (Nablas, NonEmpty Nablas)
ldiMatch (PmMatch { pm_pats = red, pm_grhss = grhss })
  = (rs_cov red, ldiGRHSs grhss)

ldiGRHSs :: PmGRHSs Post -> NonEmpty Nablas
ldiGRHSs (PmGRHSs { pgs_grhss = grhss }) = ldiGRHS <$> grhss

ldiGRHS :: PmGRHS Post -> Nablas
ldiGRHS (PmGRHS { pg_grds = red }) = rs_cov red

data CIRB = CIRB
  { cirb_cov :: !(OrdList SrcInfo)
  , cirb_inacc :: !(OrdList SrcInfo)
  , cirb_red :: !(OrdList SrcInfo)
  }

instance Semigroup CIRB where
  CIRB a b c <> CIRB d e f = CIRB (a <> d) (b <> e) (c <> f)
    where (<>) = (Semi.<>)

instance Monoid CIRB where
  mempty = CIRB mempty mempty mempty

ensureOneNotRedundant :: CIRB -> CIRB
ensureOneNotRedundant ci = case ci of
  CIRB NilOL NilOL (ConsOL r rs) -> ci { cirb_inacc = unitOL r, cirb_red = rs }
  _ -> ci

testRedSets :: RedSets -> DsM (Bool, Bool)
testRedSets RedSets { rs_cov = cov, rs_div = div } = do
  is_covered <- isInhabited cov
  may_diverge <- isInhabited div
  pure (is_covered, may_diverge)

cirbsMatchGroup :: PmMatchGroup Post -> DsM CIRB
cirbsMatchGroup (PmMatchGroup matches) = Semi.sconcat <$> traverse cirbsMatch matches

cirbsMatch :: PmMatch Post -> DsM CIRB
cirbsMatch PmMatch { pm_pats = red, pm_grhss = grhss } = do
  (_, may_diverge) <- testRedSets red
  cirb <- cirbsGRHSs grhss
  pure $ applyWhen may_diverge ensureOneNotRedundant
       $ cirb

cirbsGRHSs :: PmGRHSs Post -> DsM CIRB
cirbsGRHSs (PmGRHSs { pgs_grhss = grhss }) = Semi.sconcat <$> traverse cirbsGRHS grhss

cirbsGRHS :: PmGRHS Post -> DsM CIRB
cirbsGRHS PmGRHS { pg_grds = red, pg_rhs = info } = do
  (is_covered, may_diverge) <- testRedSets red
  let cirb | is_covered = mempty { cirb_cov = unitOL info }
           | may_diverge = mempty { cirb_inacc = unitOL info }
           | otherwise = mempty { cirb_red = unitOL info }
  pure cirb

data FormatReportWarningsMode ann where
  ReportMatchGroup :: FormatReportWarningsMode (PmMatchGroup Post)

deriving instance Eq (FormatReportWarningsMode ann)

collectInMode :: FormatReportWarningsMode ann -> ann -> DsM CIRB
collectInMode ReportMatchGroup = cirbsMatchGroup

formatReportWarnings
  :: FormatReportWarningsMode ann
  -> DsMatchContext
  -> [Id Zk]
  -> CheckResult ann
  -> DsM ()
formatReportWarnings report_mode ctx vars cr@CheckResult { cr_ret = ann } = do
  cov_info <- collectInMode report_mode ann
  dflags <- getDynFlags
  reportWarnings dflags report_mode ctx vars cr{ cr_ret = cov_info }

reportWarnings
  :: DynFlags
  -> FormatReportWarningsMode ann
  -> DsMatchContext
  -> [Id Zk]
  -> CheckResult CIRB
  -> DsM ()
reportWarnings dflags report_mode (DsMatchContext kind loc) vars
  CheckResult { cr_ret = CIRB { cirb_inacc = inaccessible_rhss, cirb_red = redundant_rhss }
              , cr_uncov = uncovered
              , cr_approx = precision }
  = when (flag_i || flag_u) $ do
      unc_examples <- getNFirstUncovered gen_mode vars (maxPatterns + 1) uncovered
      let exists_r = flag_i && notNull redundant_rhss
          exists_i = flag_i && notNull inaccessible_rhss
          exists_u = flag_u && notNull unc_examples
          approx = precision == Approximate

      when (approx && (exists_u || exists_i)) $
        panic "putSrcSpanDs loc (diagnosticDs (DsMaxPmCheckedModelsReached (maxPmCheckModels dflags)))"

      when exists_r $ forM_ redundant_rhss $ \(SrcInfo (L l q)) ->
        panic "putSrcSpanDs l (diagnosticDs (DsOverlappingPatterns kind q))"

      when exists_i $ forM_ inaccessible_rhss $ \(SrcInfo (L l q)) ->
        panic "putSrcSpanDs l (diagnosticDs (DsInaccessibleRhs kind q))"

      when exists_u $
        panic "putSrcSpanDs loc (diagnosticDs (DsNonExhaustivePatterns kind check_type maxPatterns vars unc_examples))"
      
  where
    flag_i = overlapping dflags kind
    flag_u = exhaustive dflags kind

    check_type = panic "check_type"
    gen_mode = case report_mode of
      _ -> MinimalCover

    maxPatterns = maxUncoveredPatterns dflags

getNFirstUncovered :: GenerateInhabitingPatternsMode -> [Id Zk] -> Int -> Nablas -> DsM [Nabla]
getNFirstUncovered mode vars n (MkNablas nablas) = go n (bagToList nablas)
  where
    go 0 _ = pure []
    go _ [] = pure []
    go n (nabla:nablas) = do
      panic "getNFirstuncovered"

locallyExtendPmNablas :: DsM a -> (Nablas -> DsM Nablas) -> DsM a
locallyExtendPmNablas k ext = do
  nablas <- getLdiNablas
  nablas' <- unsafeInterleaveM $ ext nablas
  updPmNablas nablas' k

addCoreScrutTmCs :: [CoreExpr] -> [Id Zk] -> DsM a -> DsM a
addCoreScrutTmCs [] _ k = k
addCoreScrutTmCs (scr:scrs) (x:xs) k
  = locallyExtendPmNablas (addCoreScrutTmCs scrs xs k) $ \nablas ->
    addPhiCtsNablas nablas (unitBag (PhiCoreCt x scr))
addCoreScrutTmCs _ _ _ = panic "addCoreScrutTmCs: numbers of scrutinees and match ids differ"

addCsScrutTmCs :: [LCsExpr Zk] -> [Id Zk] -> DsM a -> DsM a
addCsScrutTmCs scrs vars k = do
  scr_es <- traverse dsLExpr scrs
  addCoreScrutTmCs scr_es vars k
