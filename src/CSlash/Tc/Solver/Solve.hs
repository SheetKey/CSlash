module CSlash.Tc.Solver.Solve where

-- import GHC.Tc.Solver.Dict
import CSlash.Tc.Solver.Equality( solveKiEquality )
-- import GHC.Tc.Solver.Irred( solveIrred )
-- import GHC.Tc.Solver.Rewrite( rewrite )
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.TcType
-- import GHC.Tc.Types.Evidence
import CSlash.Tc.Types
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Solver.InertSet
import CSlash.Tc.Solver.Monad

-- import GHC.Core.Predicate
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

{-
**********************************************************************
*                                                                    *
*                      Main Solver                                   *
*                                                                    *
******************************************************************* -}

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

solveNC :: CtEvidence -> SolverStage Void
solveNC ev = case ctEvPred ev of
  KiEqPred ki1 ki2 -> solveKiEquality ev ki1 ki2
