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
      tracePm "desugaed matches" (ppr matches)
      result <- {-# SCC "checkMatchGroup" #-}
                unCA (checkMatchGroup matches) missing
      tracePm "}: " (ppr (cr_uncov result))
      unless False -- TODO: do notation stuff
        ({-# SCC "formatReportWarnings" #-}
          panic "formatReportWarnings ReportMatchGroup ctxt vars result")
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
