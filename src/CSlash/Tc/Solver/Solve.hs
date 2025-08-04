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

solveSimpleTyGivens :: [TyCt] -> TcS ()
solveSimpleTyGivens givens
  | null givens
  = return ()
  | otherwise
  = do traceTcS "solveSimpleTyGivens {" (ppr givens)
       solveSimples (listToBag givens) emptyBag
       traceTcS "End solveSimpleTyGivens }" empty

solveSimpleKiGivens :: [KiCt] -> TcS ()
solveSimpleKiGivens givens
  | null givens
  = return ()
  | otherwise
  = do traceTcS "solveSimpleKiGivens {" (ppr givens)
       solveSimples emptyBag (listToBag givens)
       traceTcS "End solveSimpleKiGivens }" empty

solveSimpleWanteds :: TyCts -> KiCts -> TcS WantedTyConstraints
solveSimpleWanteds ty_simples ki_simples = do
  traceTcS "solveSimpleWanteds {" (ppr ty_simples $$ ppr ki_simples)
  dflags <- getDynFlags
  (n, wtc) <- go 1 (solverIterations dflags) (emptyWC { wtc_simple = ty_simples
                                                      , wtc_wkc =
                                                        emptyWC { wkc_simple = ki_simples } })
  traceTcS "solveSimpleWanteds end }"
    $ vcat [ text "iterations =" <+> ppr n
           , text "residual =" <+> ppr wtc ]

  return wtc
  where
    go :: Int -> IntWithInf -> WantedTyConstraints -> TcS (Int, WantedTyConstraints)
    go n limit wtc
      | n `intGtLimit` limit
      = failTcS $ panic "TcRnSimplifierTooManyIterations ty_simples ki_simples limit wtc"
      | isEmptyBag (wtc_simple wtc) && isEmptyBag (wkc_simple (wtc_wkc wtc))
      = return (n, wtc)
      | otherwise
      = do wtc1 <- solve_simple_wanteds wtc
           return (n, wtc1)

solveSimpleKiWanteds :: KiCts -> TcS WantedKiConstraints
solveSimpleKiWanteds simples = do
  traceTcS "solveSimpleKiWanteds {" (ppr simples)
  dflags <- getDynFlags
  (n, wc) <- go 1 (solverIterations dflags) (emptyWC { wkc_simple = simples })
  traceTcS "solveSimpleKiWanteds end }"
    $ vcat [ text "iterations =" <+> ppr n
           , text "residual =" <+> ppr wc ]
  return wc
  where
    go :: Int -> IntWithInf -> WantedKiConstraints -> TcS (Int, WantedKiConstraints)
    go n limit wc
      | n `intGtLimit` limit
      = failTcS $ TcRnSimplifierTooManyIterations simples limit wc
      | isEmptyBag (wkc_simple wc)
      = return (n, wc)
      | otherwise
      = do wc1 <- solve_simple_ki_wanteds wc
           return (n, wc1)

solve_simple_wanteds :: WantedTyConstraints -> TcS WantedTyConstraints
solve_simple_wanteds (WTC { wtc_simple = ty_simples1, wtc_impl = ty_implics1
                          , wtc_wkc = WKC { wkc_simple = ki_simples1, wkc_impl = ki_implics1 } })
  = nestTcS $ do
      solveSimples ty_simples1 ki_simples1
      (ty_implics2, ty_unsolved, ki_implics2, ki_unsolved) <- getUnsolvedInerts
      return $ WTC { wtc_simple = ty_unsolved
                   , wtc_impl = ty_implics1 `unionBags` ty_implics2
                   , wtc_wkc = WKC { wkc_simple = ki_unsolved
                                   , wkc_impl = ki_implics1 `unionBags` ki_implics2 } }

solve_simple_ki_wanteds :: WantedKiConstraints -> TcS WantedKiConstraints
solve_simple_ki_wanteds (WKC { wkc_simple = simples1, wkc_impl = implics1 })
  = nestKiTcS $ do
      solveSimples emptyBag simples1
      (implics2, unsolved) <- getUnsolvedKiInerts
      return $ WKC { wkc_simple = unsolved
                   , wkc_impl = implics1 `unionBags` implics2 }
                  
{- *********************************************************************
*                                                                      *
           Solving flat constraints: solveSimples
*                                                                      *
********************************************************************* -}

solveSimples :: TyCts -> KiCts -> TcS ()
solveSimples ty_cts ki_cts = {-# SCC "solveSimples" #-} do
  emitKiWork ki_cts
  emitTyWork ty_cts
  solve_loop
  where
    solve_loop = {-# SCC "solve_loop" #-} do
      sel <- selectNextWorkItem
      case sel of
        Nothing -> return ()
        Just (Right kict) -> do solveOneKi kict
                                solve_loop
        Just (Left tyct) -> do panic "solveSimples tyct"

solveOneKi :: KiCt -> TcS ()
solveOneKi workItem = do
  wl <- getWorkList
  inerts <- getInertKiSet
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
    solve :: KiCt -> TcS ()
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

solveCt :: KiCt -> SolverStage Void
solveCt (CNonCanonicalKi ev) = solveNC ev
solveCt (CIrredCanKi (IrredKiCt { ikr_ev = ev })) = solveNC ev
solveCt (CKiCoCan (KiCoCt { kc_ev = ev, kc_pred = kc, kc_lhs = lhs, kc_rhs = rhs }))
  = solveKiCoercion ev kc (canKiCoLHSKind lhs) rhs

solveNC :: CtKiEvidence -> SolverStage Void
solveNC ev = case classifyPredKind (ctKiEvPred ev) of
  KiCoPred kc ki1 ki2 -> solveKiCoercion ev kc ki1 ki2
  _ -> do ev <- rewriteEvidence ev
          let irred = IrredKiCt { ikr_ev = ev, ikr_reason = IrredShapeReason }
          case classifyPredKind (ctKiEvPred ev) of
            IrredPred {} -> solveIrred irred
            KiCoPred kc ki1 ki2 -> solveKiCoercion ev kc ki1 ki2

{- *********************************************************************
*                                                                      *
                  Evidence transformation
*                                                                      *
********************************************************************* -}

rewriteEvidence :: CtKiEvidence -> SolverStage CtKiEvidence
rewriteEvidence ev = Stage $ do
  traceTcS "rewriteEvidence" (ppr ev)
  (redn, rewriters) <- rewriteKi ev (ctKiEvPred ev)
  finish_rewrite ev redn rewriters

finish_rewrite :: CtKiEvidence -> Reduction -> KiRewriterSet -> TcS (StopOrContinue CtKiEvidence)
finish_rewrite old_ev (ReductionKi co new_pred) rewriters
  | isReflKiCo co
  = assert (isEmptyKiRewriterSet rewriters)
    $ continueWith (setCtEvPredKind old_ev new_pred)

finish_rewrite ev@(CtKiGiven { ctkev_covar = old_covar, ctkev_loc = loc })
               (ReductionKi co new_pred) rewriters
  = assert (isEmptyKiRewriterSet rewriters) $ do
      new_ev <- newGivenKiCoVar loc new_pred
      continueWith new_ev

finish_rewrite ev@(CtKiWanted { ctkev_dest = dest, ctkev_loc = loc, ctkev_rewriters = rewriters })
               (ReductionKi co new_pred) new_rewriters
  = do new_ev <- newWanted loc rewriters' new_pred
       setWantedKiCo dest $ mkSymKiCo co
       continueWith new_ev
  where
    rewriters' = rewriters S.<> new_rewriters
