module CSlash.Tc.Solver.Solve where

import CSlash.Tc.Solver.Equality( solveKiCoercion )
import CSlash.Tc.Solver.Irred( solveIrred )
import CSlash.Tc.Solver.Rewrite( rewriteKi )
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Solver.InertSet
import CSlash.Tc.Solver.Monad

import CSlash.Core.Kind
import CSlash.Core.Predicate
import CSlash.Core.Reduction
-- import GHC.Core.Coercion
-- import GHC.Core.Class( classHasSCs )

import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Basic ( IntWithInf, intGtLimit )

import CSlash.Data.Bag

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc

import CSlash.Driver.Session

import Data.List( deleteFirstsBy )

import Control.Monad
import Data.Semigroup as S
import Data.Void( Void )

{- *******************************************************************
*                                                                    *
*                      Main Solver                                   *
*                                                                    *
******************************************************************* -}

solveSimpleGivens :: [Ct] -> TcS ()
solveSimpleGivens givens
  | null givens
  = return ()
  | otherwise
  = do traceTcS "solveSimpleGivens {" (ppr givens)
       solveSimples (listToBag givens)
       traceTcS "End solveSimpleGivens }" empty

solveSimpleWanteds :: Cts -> TcS WantedConstraints
solveSimpleWanteds simples = do
  traceTcS "solveSimpleWanteds {" (ppr simples)
  dflags <- getDynFlags
  (n, wc) <- go 1 (solverIterations dflags) (emptyWC { wc_simple = simples })
  traceTcS "solveSimpleWanteds end }"
    $ vcat [ text "iterations =" <+> ppr n
           , text "residual =" <+> ppr wc ]
  return wc
  where
    go :: Int -> IntWithInf -> WantedConstraints -> TcS (Int, WantedConstraints)
    go n limit wc
      | n `intGtLimit` limit
      = failTcS $ TcRnSimplifierTooManyIterations simples limit wc
      | isEmptyBag (wc_simple wc)
      = return (n, wc)
      | otherwise
      = do wc1 <- solve_simple_wanteds wc
           return (n, wc1)

solve_simple_wanteds :: WantedConstraints -> TcS WantedConstraints
solve_simple_wanteds (WC { wc_simple = simples1, wc_impl = implics1 })
  = nestTcS $ do
      solveSimples simples1
      (implics2, unsolved) <- getUnsolvedInerts
      return $ WC { wc_simple = unsolved
                  , wc_impl = implics1 `unionBags` implics2 }
                  
{- *********************************************************************
*                                                                      *
           Solving flat constraints: solveSimples
*                                                                      *
********************************************************************* -}

solveSimples :: Cts -> TcS ()
solveSimples cts = {-# SCC "solveSimples" #-} do
  emitWork cts
  solve_loop
  where
    solve_loop = {-# SCC "solve_loop" #-} do
      sel <- selectNextWorkItem
      case sel of
        Nothing -> return ()
        Just ct -> do solveOne ct
                      solve_loop

solveOne :: Ct -> TcS ()
solveOne workItem = do
  wl <- getWorkList
  inerts <- getInertSet
  tclevel <- getTcLevel
  traceTcS "----------------------------- " empty
  traceTcS "Start solver pipeline {"
    $ vcat [ text "tclevel =" <+> ppr tclevel
           , text "work item =" <+> ppr workItem
           , text "inerts =" <+> ppr inerts
           , text "rest of worklist =" <+> ppr wl ]

  bumpStepCountTcS
  solve workItem
  where
    solve :: Ct -> TcS ()
    solve ct = do
      traceTcS "solve {" $ text "workitem = " <+> ppr ct
      res <- runSolverStage (solveCt ct)
      traceTcS "end solve }" (ppr res)
      case res of
        StartAgain ct -> do traceTcS "Go round again" (ppr ct)
                            solve ct
        Stop ev s -> do traceFireTcS ev s
                        traceTcS "End solver pipeline }" empty
                        return ()

{- *********************************************************************
*                                                                      *
*              Solving one constraint: solveCt
*                                                                      *
********************************************************************* -} 

solveCt :: Ct -> SolverStage Void
solveCt (CNonCanonical ev) = solveNC ev
solveCt (CIrredCan (IrredCt { ir_ev = ev })) = solveNC ev
solveCt (CKiCoCan (KiCoCt { kc_ev = ev, kc_pred = kc, kc_lhs = lhs, kc_rhs = rhs }))
  = solveKiCoercion ev kc (canKiCoLHSKind lhs) rhs

solveNC :: CtEvidence -> SolverStage Void
solveNC ev = case classifyPredKind (ctEvPred ev) of
  KiCoPred kc ki1 ki2 -> solveKiCoercion ev kc ki1 ki2
  _ -> do ev <- rewriteEvidence ev
          let irred = IrredCt { ir_ev = ev, ir_reason = IrredShapeReason }
          case classifyPredKind (ctEvPred ev) of
            IrredPred {} -> solveIrred irred
            KiCoPred kc ki1 ki2 -> solveKiCoercion ev kc ki1 ki2

{- *********************************************************************
*                                                                      *
                  Evidence transformation
*                                                                      *
********************************************************************* -}

rewriteEvidence :: CtEvidence -> SolverStage CtEvidence
rewriteEvidence ev = Stage $ do
  traceTcS "rewriteEvidence" (ppr ev)
  (redn, rewriters) <- rewriteKi ev (ctEvPred ev)
  finish_rewrite ev redn rewriters

finish_rewrite :: CtEvidence -> Reduction -> RewriterSet -> TcS (StopOrContinue CtEvidence)
finish_rewrite old_ev (ReductionKi co new_pred) rewriters
  | isReflKiCo co
  = assert (isEmptyRewriterSet rewriters)
    $ continueWith (setCtEvPredKind old_ev new_pred)

finish_rewrite ev@(CtGiven { ctev_covar = old_covar, ctev_loc = loc })
               (ReductionKi co new_pred) rewriters
  = assert (isEmptyRewriterSet rewriters) $ do
      new_ev <- newGivenKiCoVar loc new_pred
      continueWith new_ev

finish_rewrite ev@(CtWanted { ctev_dest = dest, ctev_loc = loc, ctev_rewriters = rewriters })
               (ReductionKi co new_pred) new_rewriters
  = do new_ev <- newWanted loc rewriters' new_pred
       setWantedKiCo dest $ mkSymKiCo co
       continueWith new_ev
  where
    rewriters' = rewriters S.<> new_rewriters
