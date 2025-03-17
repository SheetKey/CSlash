module CSlash.Tc.Solver.Irred where

import CSlash.Tc.Types.Constraint
import CSlash.Tc.Solver.InertSet
-- import GHC.Tc.Solver.Dict( matchLocalInst, chooseInstance )
import CSlash.Tc.Solver.Monad
import CSlash.Tc.Types.Evidence

-- import GHC.Core.Coercion

import CSlash.Types.Basic ( SwapFlag(..) )

import CSlash.Utils.Outputable

import CSlash.Data.Bag

import Data.Void ( Void )

{- *********************************************************************
*                                                                      *
*                      Irreducibles
*                                                                      *
********************************************************************* -}

solveIrred :: IrredCt -> SolverStage Void
solveIrred irred = do
  simpleStage $ traceTcS "solveIrred:" (ppr irred)
  tryInertIrreds irred
  tryQCsIrredCt irred
  simpleStage (updInertIrreds irred)
  stopWithStage (irredCtEvidence irred) "Kept inert IrredCt"

updInertIrreds :: IrredCt -> TcS ()
updInertIrreds irred = do
  tc_lvl <- getTcLevel
  updInertCans $ addIrredToCans tc_lvl irred

{- *********************************************************************
*                                                                      *
*                      Inert Irreducibles
*                                                                      *
********************************************************************* -}

tryInertIrreds :: IrredCt -> SolverStage ()
tryInertIrreds irred = Stage $ do
  ics <- getInertCans
  try_inert_irreds ics irred

try_inert_irreds :: InertCans -> IrredCt -> TcS (StopOrContinue ())
try_inert_irreds inerts irred_w@(IrredCt { ir_ev = ev_w, ir_reason = reason })
  | let (matching_irreds, others) = findMatchingIrreds (inert_irreds inerts) ev_w
  , ((irred_i, swap) : _) <- bagToList matching_irreds
  , let ev_i = irredCtEvidence irred_i
        ct_i = CIrredCan irred_i
        ct_w = CIrredCan irred_w
  , not (isInsolubleReason reason) || isGiven ev_i || isGiven ev_w
  = do traceTcS "iteractIrred"
         $ vcat [ text "wanted:" <+> (ppr ct_w $$ ppr (ctOrigin ct_w))
                , text "inert: " <+> (ppr ct_i $$ ppr (ctOrigin ct_i)) ]
       case solveOneFromTheOther ct_i ct_w of
         KeepInert -> return $ Stop ev_w (text "Irred equal:KeptInert" <+> ppr ct_w)
         KeepWork -> do updInertCans (updIrreds (\_ -> others))
                        continueWith ()
  | otherwise
  = continueWith ()

{- *********************************************************************
*                                                                      *
*                      Quantified constraints
*                                                                      *
********************************************************************* -}

tryQCsIrredCt :: IrredCt -> SolverStage ()
tryQCsIrredCt (IrredCt { ir_ev = ev })
  | isGiven ev
  = Stage $ continueWith ()
  | otherwise
  = Stage $ continueWith ()
