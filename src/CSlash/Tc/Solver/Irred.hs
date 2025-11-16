module CSlash.Tc.Solver.Irred where

import CSlash.Core.Type.Rep (AnyTypeCoercion, mkSymTyCo)
import CSlash.Core.Kind (mkSymKiCo)

import CSlash.Tc.Types.Constraint
import CSlash.Tc.Solver.InertSet
-- import GHC.Tc.Solver.Dict( matchLocalInst, chooseInstance )
import CSlash.Tc.Solver.Monad
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Utils.TcType (AnyKindCoercion)

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

solveIrredTy :: IrredTyCt -> TySolverStage Void
solveIrredTy irred = do
  simpleStage $ traceTcS "solveIrredTy:" (ppr irred)
  tryInertIrredTys irred
  tryQCsIrredTyCt irred
  simpleStage (updInertIrredTys irred)
  stopWithStage (irredTyCtEvidence irred) "Kept inert IrredTyCt"

updInertIrredTys :: IrredTyCt -> TcS ()
updInertIrredTys irred = do
  tc_lvl <- getTcLevel
  updInertTyCans $ addIrredTyToCans tc_lvl irred

solveIrredKi :: IrredKiCt -> KiSolverStage Void
solveIrredKi irred = do
  simpleStage $ traceTcS "solveIrred:" (ppr irred)
  tryInertIrredKis irred
  tryQCsIrredKiCt irred
  simpleStage (updInertIrredKis irred)
  stopWithStage (irredKiCtEvidence irred) "Kept inert IrredKiCt"

updInertIrredKis :: IrredKiCt -> TcS ()
updInertIrredKis irred = do
  tc_lvl <- getTcLevel
  updInertKiCans $ addIrredKiToCans tc_lvl irred

{- *********************************************************************
*                                                                      *
*                      Inert Irreducibles
*                                                                      *
********************************************************************* -}

tryInertIrredTys :: IrredTyCt -> TySolverStage ()
tryInertIrredTys irred = Stage $ do
  ics <- getInertTyCans
  try_inert_irred_tys ics irred

tryInertIrredKis :: IrredKiCt -> KiSolverStage ()
tryInertIrredKis irred = Stage $ do
  ics <- getInertKiCans
  try_inert_irred_kis ics irred

try_inert_irred_tys :: InertTyCans -> IrredTyCt -> TcS (StopOrContinueTy ())
try_inert_irred_tys inerts irred_w@(IrredTyCt { itr_ev = ev_w, itr_reason = reason })
  | let (matching_irreds, others) = findMatchingIrredTys (inert_ty_irreds inerts) ev_w
  , ((irred_i, swap) : _) <- bagToList matching_irreds
  , let ev_i = irredTyCtEvidence irred_i
        ct_i = CIrredCanTy irred_i
        ct_w = CIrredCanTy irred_w
  , not (isInsolubleReason reason) || isGiven ev_i || isGiven ev_w
  = do traceTcS "iteractIrred"
         $ vcat [ text "wanted:" <+> (ppr ct_w $$ ppr (ctOrigin ct_w))
                , text "inert:" <+> (ppr ct_i $$ ppr (ctOrigin ct_i)) ]
       case solveOneTyFromTheOther ct_i ct_w of
         KeepInert -> do
           setTyCoBindIfWanted ev_w (swap_me swap ev_i)
           return $ Stop ev_w (text "Irred equal:KeepInert" <+> ppr ct_w)
         KeepWork -> do
           setTyCoBindIfWanted ev_i (swap_me swap ev_w)
           updInertTyCans (updIrredTys (\_ -> others))
           continueWith ()
  | otherwise
  = continueWith ()
  where
    swap_me :: SwapFlag -> CtTyEvidence -> AnyTypeCoercion
    swap_me swap ev
      = case swap of
          NotSwapped -> ctEvTyCoercion ev
          IsSwapped -> mkSymTyCo $ ctEvTyCoercion ev

try_inert_irred_kis :: InertKiCans -> IrredKiCt -> TcS (StopOrContinueKi ())
try_inert_irred_kis inerts irred_w@(IrredKiCt { ikr_ev = ev_w, ikr_reason = reason })
  | let (matching_irreds, others) = findMatchingIrredKis (inert_ki_irreds inerts) ev_w
  , ((irred_i, swap) : _) <- bagToList matching_irreds
  , let ev_i = irredKiCtEvidence irred_i
        ct_i = CIrredCanKi irred_i
        ct_w = CIrredCanKi irred_w
  , not (isInsolubleReason reason) || isGiven ev_i || isGiven ev_w
  = do traceTcS "iteractIrred"
         $ vcat [ text "wanted:" <+> (ppr ct_w $$ ppr (ctOrigin ct_w))
                , text "inert: " <+> (ppr ct_i $$ ppr (ctOrigin ct_i)) ]
       case solveOneKiFromTheOther ct_i ct_w of
         KeepInert -> do
           setKiCoBindIfWanted ev_w (swap_me swap ev_i)
           return $ Stop ev_w (text "Irred equal:KeepInert" <+> ppr ct_w)
         KeepWork -> do
           setKiCoBindIfWanted ev_i (swap_me swap ev_w)
           updInertKiCans (updIrredKis (\_ -> others))
           continueWith ()
  | otherwise
  = continueWith ()
  where
    swap_me :: SwapFlag -> CtKiEvidence -> AnyKindCoercion
    swap_me swap ev
      = case swap of
          NotSwapped -> ctEvKiCoercion ev
          IsSwapped -> mkSymKiCo $ ctEvKiCoercion ev

{- *********************************************************************
*                                                                      *
*                      Quantified constraints
*                                                                      *
********************************************************************* -}

tryQCsIrredKiCt :: IrredKiCt -> KiSolverStage ()
tryQCsIrredKiCt (IrredKiCt { ikr_ev = ev }) 
  | isGiven ev
  = Stage $ continueWith ()
  | otherwise
  = Stage $ continueWith ()

-- need to implement if I ever allow user code to specify `t1 ~ t2` or similar
tryQCsIrredTyCt :: IrredTyCt -> TySolverStage ()
tryQCsIrredTyCt (IrredTyCt { itr_ev = ev }) 
  | isGiven ev
  = Stage $ continueWith ()
  | otherwise
  = Stage $ continueWith ()
