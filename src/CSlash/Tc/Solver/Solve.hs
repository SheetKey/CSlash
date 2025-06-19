module CSlash.Tc.Solver.Solve where

import CSlash.Tc.Solver.Relation
import CSlash.Tc.Solver.Equality( solveKiEquality )
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
solveCt (CEqCan (KiEqCt { eq_ev = ev, eq_lhs = lhs, eq_rhs = rhs }))
  = solveKiEquality ev (canKiEqLHSKind lhs) rhs
solveCt (CRelCan (RelCt { rl_ev = ev })) = do
  ev <- rewriteEvidence ev
  case classifyPredKind (ctEvPred ev) of
    RelPred kc k1 k2 -> solveRel (RelCt { rl_ev = ev, rl_kc = kc, rl_ki1 = k1, rl_ki2 = k2 })
    _ -> pprPanic "solveCt" (ppr ev)

solveNC :: CtEvidence -> SolverStage Void
solveNC ev = case classifyPredKind (ctEvPred ev) of
  EqPred ki1 ki2 -> solveKiEquality ev ki1 ki2
  _ -> do ev <- rewriteEvidence ev
          let irred = IrredCt { ir_ev = ev, ir_reason = IrredShapeReason }
          case classifyPredKind (ctEvPred ev) of
            RelPred kc ki1 ki2 -> solveRelNC ev kc ki1 ki2
            IrredPred {} -> solveIrred irred
            EqPred ki1 ki2 -> solveKiEquality ev ki1 ki2

{- *********************************************************************
*                                                                      *
                  Evidence transformation
*                                                                      *
********************************************************************* -}

rewriteEvidence :: CtEvidence -> SolverStage CtEvidence
rewriteEvidence ev = Stage $ do
  traceTcS "rewriteEvidence" (ppr ev)
  (redn, rewriters) <- panic "rewriteKi ev (ctEvPred ev)"
  finish_rewrite ev redn rewriters

finish_rewrite :: CtEvidence -> Reduction -> RewriterSet -> TcS (StopOrContinue CtEvidence)
finish_rewrite old_ev (ReductionKi co new_pred) rewriters
  | isReflKiCo co
  = assert (isEmptyRewriterSet rewriters)
    $ continueWith (panic "setCtEvPredKind old_ev new_pred")

finish_rewrite ev@(CtGiven { ctev_evar = old_evar, ctev_loc = loc })
               (ReductionKi co new_pred) rewriters
  = assert (isEmptyRewriterSet rewriters) $ do
      new_ev <- panic "newGivenKiEvVar loc (new_pred, new_ty)"
      continueWith new_ev
  where
    new_ty = panic "mkKiEvCast (kiEvVar old_evar) co"

finish_rewrite ev@(CtWanted { ctev_dest = dest, ctev_loc = loc, ctev_rewriters = rewriters })
               (ReductionKi co new_pred) new_rewriters
  = do mb_new_ev <- panic "newWanted loc rewriters' new_pred"
       setWantedKiEvType dest True $
         panic "mkKiEvCast (getKiEvType mb_new_ev) (mkSymKiCo co)"
       case mb_new_ev of
         Fresh new_ev -> continueWith new_ev
         Cached _ -> stopWith ev "Cached wanted"
  where
    rewriters' = rewriters S.<> new_rewriters
