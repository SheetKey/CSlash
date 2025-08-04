module CSlash.Tc.Solver.Equality (solveKiCoercion) where

import CSlash.Tc.Solver.Irred( solveIrred )
-- import GHC.Tc.Solver.Dict( matchLocalInst, chooseInstance )
import CSlash.Tc.Solver.Rewrite
import CSlash.Tc.Solver.Monad
import CSlash.Tc.Solver.InertSet
-- import GHC.Tc.Solver.Types( findFunEqsByTyCon )
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.Unify
import CSlash.Tc.Utils.TcType
-- import GHC.Tc.Instance.Family ( tcTopNormaliseNewTypeTF_maybe )
-- import GHC.Tc.Instance.FunDeps( FunDepEqn(..) )
import qualified CSlash.Tc.Utils.Monad as TcM

import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.Kind.Compare
import CSlash.Core.Predicate
-- import GHC.Core.Class
import CSlash.Core.DataCon ( dataConName )
import CSlash.Core.TyCon
import CSlash.Core.Type.Rep
-- import GHC.Core.Coercion
-- import GHC.Core.Coercion.Axiom
import CSlash.Core.Reduction
-- import GHC.Core.Unify( tcUnifyTyWithTFs )
-- import GHC.Core.FamInstEnv ( FamInstEnvs, FamInst(..), apartnessCheck
--                            , lookupFamInstEnvByTyCon )
import CSlash.Core

import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set( anyVarSet )
import CSlash.Types.Name.Reader
import CSlash.Types.Basic

-- import CSlash.Builtin.Types ( anyTypeOfKind )

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc
import CSlash.Utils.Monad
import CSlash.Utils.Constants( debugIsOn )

import CSlash.Data.Pair
import CSlash.Data.Bag
import Control.Monad
import Data.Maybe ( isJust, isNothing )
import Data.List  ( zip4 )

import qualified Data.Semigroup as S
import Data.Bifunctor ( bimap )
import Data.Void( Void )

{- *********************************************************************
*                                                                      *
*        Equalities
*                                                                      *
********************************************************************* -}

solveKiCoercion :: CtKiEvidence -> KiPredCon -> AnyMonoKind -> AnyMonoKind -> SolverStage Void
solveKiCoercion ev rel ki1 ki2 = do
  Pair ki1' ki2' <- if rel /= LTKi
                    then zonkEqKinds ev ki1 ki2
                    else return $ Pair ki1 ki2
  let ev' | debugIsOn = setCtEvPredKind ev $ mkKiCoPred rel ki1' ki2'
          | otherwise = ev

  mb_canon <- canonicalizeKiCoercion ev' rel ki1' ki2'

  case mb_canon of
    Left irred_ct -> do tryQCsIrredKiCoCt irred_ct
                        solveIrred irred_ct
    Right kico_ct -> do tryInertKiCos kico_ct
                        tryQCsKiCoCt kico_ct
                        simpleStage (updInertKiCos kico_ct)
                        stopWithStage (kiCoCtEvidence kico_ct) "Kept inert EqCt"

updInertKiCos :: KiCoCt -> TcS ()
updInertKiCos kico_ct = do
  kickOutRewritable (KOAfterAdding (kiCoCtLHS kico_ct)) (kiCoCtFlavor kico_ct)
  tc_lvl <- getTcLevel
  updInertCans (addKiCoToCans tc_lvl kico_ct)

{- *********************************************************************
*                                                                      *
*           zonkEqKinds
*                                                                      *
********************************************************************* -}

zonkEqKinds :: CtKiEvidence -> AnyMonoKind -> AnyMonoKind -> SolverStage (Pair AnyMonoKind)
zonkEqKinds ev ki1 ki2 = Stage $ do
  res <- go_mono ki1 ki2
  case res of
    Left pair -> continueWith pair
    Right ki -> canKiCoReflexive ev ki
  where
    go_mono :: AnyMonoKind -> AnyMonoKind -> TcS (Either (Pair AnyMonoKind) AnyMonoKind)
    go_mono (KiVarKi kv1) (KiVarKi kv2) = kivar_kivar kv1 kv2
    go_mono (KiVarKi kv1) ki2 = kivar NotSwapped kv1 ki2
    go_mono ki1 (KiVarKi kv2) = kivar IsSwapped kv2 ki1

    go_mono ki1@(BIKi kc1) (BIKi kc2)
      | kc1 == kc2
      = return $ Right ki1

    go_mono (FunKi f1 arg1 res1) (FunKi f2 arg2 res2)
      | f1 == f2
      = do res_a <- go_mono arg1 arg2
           res_b <- go_mono res1 res2
           return $ combine_rev (FunKi f1) res_b res_a
    go_mono ki1 ki2 = bale_out ki1 ki2

    bale_out ki1 ki2 = return $ Left (Pair ki1 ki2)

    kivar :: SwapFlag -> AnyKiVar -> AnyMonoKind -> TcS (Either (Pair AnyMonoKind) AnyMonoKind)
    kivar swapped kv ki = case handleAnyKv (const Nothing) (Just . tcVarDetails) kv of
      Just (MetaVar { mv_ref = ref }) -> do
        cts <- readTcRef ref
        case cts of
          Flexi -> give_up
          Indirect ki' -> do
            trace_indirect kv ki'
            unSwap swapped go_mono ki' ki
      _ -> give_up
      where
        give_up = return $ Left $ unSwap swapped Pair (mkKiVarKi kv) ki

    kivar_kivar kv1 kv2
      | kv1 == kv2 = return $ Right (mkKiVarKi kv1)
      | otherwise = do (ki1', progress1) <- quick_zonk kv1
                       (ki2', progress2) <- quick_zonk kv2
                       if progress1 || progress2
                         then go_mono ki1' ki2'
                         else return $ Left (Pair (KiVarKi kv1) (KiVarKi kv2))

    trace_indirect kv ki
      = traceTcS "Following filled kivar (zonkEqKinds)"
                 (ppr kv <+> equals <+> ppr ki)

    quick_zonk kv = case handleAnyKv (const Nothing) (Just . tcVarDetails) kv of
      Just (MetaVar { mv_ref = ref }) -> do
        cts <- readTcRef ref
        case cts of
          Flexi -> return (KiVarKi kv, False)
          Indirect ki' -> do trace_indirect kv ki'
                             return (ki', True)
      _ -> return (KiVarKi kv, False)

    combine_results :: [Either (Pair AnyMonoKind) AnyMonoKind]
                    -> Either (Pair [AnyMonoKind]) [AnyMonoKind]
    combine_results = bimap (fmap reverse) reverse .
                      foldl' (combine_rev (:)) (Right [])
                      
    combine_rev :: (a -> b -> c) -> Either (Pair b) b -> Either (Pair a) a -> Either (Pair c) c
    combine_rev f (Left list) (Left elt) = Left (f <$> elt <*> list)
    combine_rev f (Left list) (Right ki) = Left (f <$> pure ki <*> list)
    combine_rev f (Right kis) (Left elt) = Left (f <$> elt <*> pure kis)
    combine_rev f (Right kis) (Right ki) = Right (f ki kis)

{- *********************************************************************
*                                                                      *
*           canonicaliseKiCoercion
*                                                                      *
********************************************************************* -}

canonicalizeKiCoercion
  :: CtKiEvidence
  -> KiPredCon
  -> AnyMonoKind
  -> AnyMonoKind
  -> SolverStage (Either IrredKiCt KiCoCt)
canonicalizeKiCoercion ev kc ki1 ki2 = Stage $ do
  traceTcS "canonicalizeKiCoercion"
    $ vcat [ ppr ev, ppr kc, ppr ki1, ppr ki2 ]
  rdr_env <- getGlobalRdrEnvTcS
  can_ki_co_nc False rdr_env ev kc ki1 ki2

can_ki_co_nc
  :: Bool
  -> GlobalRdrEnv
  -> CtKiEvidence
  -> KiPredCon
  -> AnyMonoKind
  -> AnyMonoKind
  -> TcS (StopOrContinue (Either IrredKiCt KiCoCt))

can_ki_co_nc _ _ ev kc ki1@(BIKi kc1) (BIKi kc2) 
  | kc1 == kc2
  , kc == EQKi
  = canKiCoReflexive ev ki1
  | kc1 == kc2
  , kc == LTEQKi
  = canKiCoLiftReflexive ev ki1
  | kc1 < kc2
  , kc == LTEQKi
  = canKiCoLiftLT ev kc1 kc2
  | kc1 < kc2
  , kc == LTKi
  = canKiCoLT ev kc1 kc2

can_ki_co_nc True _ ev kc ki1 ki2
  | ki1 `tcEqMonoKind` ki2
  , kc == EQKi
  = canKiCoReflexive ev ki1
  | ki1 `tcEqMonoKind` ki2
  , kc == LTEQKi
  = canKiCoLiftReflexive ev ki1

can_ki_co_nc True _ ev kc ki1 ki2
  | ki1 `tcLTEQMonoKind` ki2
  , kc == LTEQKi
  = canKiCoBILTEQ ev ki1 ki2

----------------------
-- Otherwise try to decompose
----------------------

can_ki_co_nc _ _ ev kc (FunKi f1 ki1a ki1b) (FunKi f2 ki2a ki2b)
  | f1 == f2
  = canDecomposableFunKi ev kc f1 (ki1a, ki1b) (ki2a, ki2b)

can_ki_co_nc _ _ ev kc (KiPredApp kc1 ka1 kb1) (KiPredApp kc2 ka2 kb2)
  = panic "canKiConApp ev kc kc1 kis1 kc2 kis2" -- this souldn't really happen (need to refactor kind to prevent this)

------------------
-- Can't decompose
------------------

can_ki_co_nc False rdr_env ev kc ps_ki1 ps_ki2 = do
  (redn1@(ReductionKi _ xi1), rewriters1) <- rewriteKi ev ps_ki1
  (redn2@(ReductionKi _ xi2), rewriters2) <- rewriteKi ev ps_ki2
  new_ev <- rewriteKiCoEvidence (rewriters1 S.<> rewriters2) ev NotSwapped redn1 redn2
  traceTcS "can_ki_co_nc: go round again" (ppr new_ev $$ ppr xi1 $$ ppr xi2)
  can_ki_co_nc True rdr_env new_ev kc xi1 xi2

can_ki_co_nc True _ ev kc ki1 ki2
  | Just can_co_lhs1 <- canKiCoLHS_maybe ki1
  = do traceTcS "can_ki_co1" (ppr ki1 $$ ppr ki2)
       canKiCoCanLHSHomo ev NotSwapped kc can_co_lhs1 ki1 ki2 ki2

  | Just can_co_lhs2 <- canKiCoLHS_maybe ki2
  = do traceTcS "can_ki_co2" (ppr ki1 $$ ppr ki2)
       canKiCoCanLHSHomo ev IsSwapped kc can_co_lhs2 ki2 ki1 ki1

------------------
-- Failed
------------------

can_ki_co_nc True _ ev kc ps_ki1 ps_ki2 = do
  traceTcS "can_ki_co_nc catch-all case" (ppr kc $$ ppr ps_ki1 $$ ppr ps_ki2)
  finishCanWithIrred ShapeMismatchReason ev

canDecomposableFunKi
  :: CtKiEvidence
  -> KiPredCon
  -> FunKiFlag
  -> (AnyMonoKind, AnyMonoKind)
  -> (AnyMonoKind, AnyMonoKind)
  -> TcS (StopOrContinue a)
canDecomposableFunKi ev kc f f1@(a1, r1) f2@(a2, r2) = do
  massertPpr (kc == EQKi)
    $ vcat [ text "canDecomposableFunKi has non-equality constraint"
           , ppr ev, ppr kc, ppr f1, ppr f2 ]
  traceTcS "canDecomposableFunKi"
    $ ppr ev $$ ppr f1 $$ ppr f2
  case ev of
    CtKiWanted { ctkev_dest = dest } -> do
      (co, _, _) <- wrapUnifierTcS ev $ \uenv -> do
        arg <- uKind uenv EQKi a1 a2
        res <- uKind uenv EQKi r1 r2
        return $ mkFunKiCo f arg res
      setWantedKiCo dest co
    CtKiGiven { ctkev_covar = covar } -> pprPanic "canDecomposableFunKi"
                                     $ vcat [ ppr ev, ppr f1, ppr f2 ]
  stopWith ev "Decomposed FunKi"

canKiCoHardFailure
  :: CtKiEvidence
  -> AnyMonoKind
  -> AnyMonoKind
  -> TcS (StopOrContinue (Either IrredKiCt a))
canKiCoHardFailure ev ki1 ki2 = do
  traceTcS "canKiCoHardFailure" (ppr ki1 $$ ppr ki2)
  (redn1, rewriters1) <- rewriteKiForErrors ev ki1
  (redn2, rewriters2) <- rewriteKiForErrors ev ki2
  new_ev <- rewriteKiCoEvidence (rewriters1 S.<> rewriters2) ev NotSwapped redn1 redn2
  finishCanWithIrred ShapeMismatchReason new_ev

canKiCoCanLHSHomo
  :: CtKiEvidence
  -> SwapFlag
  -> KiPredCon
  -> CanKiCoLHS
  -> AnyMonoKind
  -> AnyMonoKind
  -> AnyMonoKind
  -> TcS (StopOrContinue (Either IrredKiCt KiCoCt))
canKiCoCanLHSHomo ev swapped kc lhs1 ps_xi1 xi2 ps_xi2
  | Just lhs2 <- canKiCoLHS_maybe xi2
  = canKiCoCanLHS2 ev swapped lhs1 ps_xi1 lhs2 ps_xi2
  | otherwise
  = canKiCoCanLHSFinish ev swapped lhs1 ps_xi2

canKiCoCanLHS2
  :: CtKiEvidence
  -> SwapFlag
  -> CanKiCoLHS
  -> AnyMonoKind
  -> CanKiCoLHS
  -> AnyMonoKind
  -> TcS (StopOrContinue (Either IrredKiCt KiCoCt))
canKiCoCanLHS2 ev swapped lhs1 ps_xi1 lhs2 ps_xi2
  | lhs1 `eqCanKiCoLHS` lhs2
  = canKiCoReflexive ev lhs1_ki
  | KiVarLHS kv1 <- lhs1
  , KiVarLHS kv2 <- lhs2
  = do traceTcS "canEqLHS2 swapOver" (ppr kv1 $$ ppr kv2 $$ ppr swapped)
       if swapOverKiVars (isGiven ev) kv1 kv2
         then finish_with_swapping
         else finish_without_swapping

  where
    lhs1_ki = canKiCoLHSKind lhs1
    lhs2_ki = canKiCoLHSKind lhs2

    finish_without_swapping = canKiCoCanLHSFinish ev swapped lhs1 ps_xi2

    finish_with_swapping = do
      new_ev <- rewriteKiCoEvidence
                emptyKiRewriterSet ev swapped (mkReflRednKi lhs1_ki) (mkReflRednKi lhs2_ki)
      canKiCoCanLHSFinish new_ev IsSwapped lhs2 ps_xi1

canKiCoCanLHSFinish
  :: CtKiEvidence
  -> SwapFlag
  -> CanKiCoLHS
  -> AnyMonoKind
  -> TcS (StopOrContinue (Either IrredKiCt KiCoCt))
canKiCoCanLHSFinish ev swapped lhs rhs = do
  traceTcS "canKiCoCanLHSFinish"
    $ vcat [ text "ev:" <+> ppr ev
           , text "swapped:" <+> ppr swapped
           , text "lhs:" <+> ppr lhs
           , text "rhs:" <+> ppr rhs ]

  canKiCoCanLHSFinish_try_unification ev swapped lhs rhs

canKiCoCanLHSFinish_try_unification
  :: CtKiEvidence
  -> SwapFlag
  -> CanKiCoLHS
  -> AnyMonoKind
  -> TcS (StopOrContinue (Either IrredKiCt KiCoCt))
canKiCoCanLHSFinish_try_unification ev swapped lhs rhs
  | isWanted ev
  , KiVarLHS kv <- lhs
  = do given_eq_lvl <- getInnermostGivenKiCoLevel
       case toTcKiVar_maybe kv of
         Just kv
           | touchabilityAndShapeTestKind given_eq_lvl kv rhs
             -> do check_result <- checkTouchableKiVarEq ev kv rhs
                   case check_result of
                     PuFail reason
                       | reason `ctkerHasOnlyProblems` do_not_prevent_rewriting
                         -> canKiCoCanLHSFinish_no_unification ev swapped lhs rhs
                       | otherwise
                         -> tryIrredInstead reason ev swapped lhs rhs
                     PuOK _ rhs_redn ->
                       do let kv_ki = mkKiVarKi $ toAnyKiVar kv
                          new_ev <- if isReflKiCo (reductionKindCoercion rhs_redn)
                                    then return ev
                                    else rewriteKiCoEvidence emptyKiRewriterSet
                                         ev swapped (mkReflRednKi kv_ki) rhs_redn
                          let final_rhs = reductionReducedKind rhs_redn
                   
                          traceTcS "Sneaky unification:"
                            $ text "Unifies:" <+> ppr kv <+> text ":=" <+> ppr final_rhs
                   
                          unifyKiVar kv final_rhs
                   
                          kickOutAfterUnification [kv]
                   
                          return $ Stop new_ev (text "Solved by unification")
                          
         _ -> canKiCoCanLHSFinish_no_unification ev swapped lhs rhs
  | otherwise
  = canKiCoCanLHSFinish_no_unification ev swapped lhs rhs
  where
    do_not_prevent_rewriting = ctkeProblem ctkeSkolemEscape S.<> ctkeProblem ctkeConcrete

canKiCoCanLHSFinish_no_unification
  :: CtKiEvidence
  -> SwapFlag
  -> CanKiCoLHS
  -> AnyMonoKind
  -> TcS (StopOrContinue (Either IrredKiCt KiCoCt))
canKiCoCanLHSFinish_no_unification ev swapped lhs rhs = do
  check_result <- checkKindEq ev lhs rhs
  case check_result of
    PuFail reason -> tryIrredInstead reason ev swapped lhs rhs
    PuOK _ rhs_redn -> do
      let lhs_ki = canKiCoLHSKind lhs
      new_ev <- rewriteKiCoEvidence emptyKiRewriterSet ev swapped (mkReflRednKi lhs_ki) rhs_redn
      continueWith $ Right $ KiCoCt { kc_ev = new_ev
                                    , kc_lhs = lhs
                                    , kc_rhs = reductionReducedKind rhs_redn
                                    , kc_pred = panic "kc_rel" }

tryIrredInstead
  :: CheckTyKiEqResult
  -> CtKiEvidence
  -> SwapFlag
  -> CanKiCoLHS
  -> AnyMonoKind
  -> TcS (StopOrContinue (Either IrredKiCt a))
tryIrredInstead reason ev swapped lhs rhs = do
  traceTcS "cantMakeCaconical" (ppr reason $$ ppr lhs $$ ppr rhs)
  new_ev <- rewriteKiCoEvidence
            emptyKiRewriterSet ev swapped (mkReflRednKi $ canKiCoLHSKind lhs) (mkReflRednKi rhs)
  finishCanWithIrred (NonCanonicalReason reason) new_ev

finishCanWithIrred :: CtIrredReason -> CtKiEvidence -> TcS (StopOrContinue (Either IrredKiCt a))
finishCanWithIrred reason ev = do
  when (isInsolubleReason reason) tryEarlyAbortTcS
  continueWith $ Left $ IrredKiCt { ikr_ev = ev, ikr_reason = reason }

canKiCoReflexive :: CtKiEvidence -> AnyMonoKind -> TcS (StopOrContinue a)
canKiCoReflexive ev ki = do
  setKiCoBindIfWanted ev $ mkReflKiCo ki
  stopWith ev "Solved by reflexivity"

canKiCoLiftReflexive :: CtKiEvidence -> AnyMonoKind -> TcS (StopOrContinue a)
canKiCoLiftReflexive ev ki = do
  setKiCoBindIfWanted ev $ LiftEq $ mkReflKiCo ki
  stopWith ev "Solved by lifting reflexivity"

canKiCoLT :: CtKiEvidence -> BuiltInKi -> BuiltInKi -> TcS (StopOrContinue a)
canKiCoLT ev kc1 kc2 = do
  let co = case (kc1, kc2) of
             (UKd, AKd) -> BI_U_A
             (AKd, LKd) -> BI_A_L
             (UKd, LKd) -> TransCo BI_U_A BI_A_L
             _ -> pprPanic "canKiCoLT" (ppr ev $$ ppr kc1 $$ ppr kc2)
  setKiCoBindIfWanted ev $ co
  stopWith ev "Solved by built-in"

canKiCoLiftLT :: CtKiEvidence -> BuiltInKi -> BuiltInKi -> TcS (StopOrContinue a)
canKiCoLiftLT ev kc1 kc2 = do
  let co = case (kc1, kc2) of
             (UKd, AKd) -> BI_U_A
             (AKd, LKd) -> BI_A_L
             (UKd, LKd) -> TransCo BI_U_A BI_A_L
             _ -> pprPanic "canKiCoLT" (ppr ev $$ ppr kc1 $$ ppr kc2)
  setKiCoBindIfWanted ev $ LiftLT co
  stopWith ev "Solved by lifting built-in"
 
canKiCoBILTEQ :: CtKiEvidence -> AnyMonoKind -> AnyMonoKind -> TcS (StopOrContinue a)
canKiCoBILTEQ ev k1 k2 = do
  let co = case (k1, k2) of
             (BIKi UKd, _) -> BI_U_LTEQ k2
             (_, BIKi LKd) -> BI_LTEQ_L k1
             _ -> pprPanic "canKiCoBILTEQ" (ppr ev $$ ppr k1 $$ ppr k2)
  setKiCoBindIfWanted ev co
  stopWith ev "Solved by built-in"

{- *******************************************************************
*                                                                    *
                   Rewriting evidence
*                                                                    *
******************************************************************* -}

rewriteKiCoEvidence
  :: KiRewriterSet
  -> CtKiEvidence
  -> SwapFlag
  -> Reduction
  -> Reduction
  -> TcS CtKiEvidence
rewriteKiCoEvidence new_rewriters old_ev swapped (ReductionKi lhs_co nlhs) (ReductionKi rhs_co nrhs)
  | NotSwapped <- swapped
  , isReflKiCo lhs_co
  , isReflKiCo rhs_co
  = return $ setCtEvPredKind old_ev new_pred
  | CtKiGiven { ctkev_covar = old_covar } <- old_ev
  = panic "rewriteKiCoEvidence"
  | CtKiWanted { ctkev_dest = dest, ctkev_rewriters = rewriters } <- old_ev
  , let rewriters' = rewriters S.<> new_rewriters
  = do (new_ev, hole_co) <- newWantedKiCo_swapped loc rewriters' kc swapped nlhs nrhs
       let co = maybeSymCo swapped $ lhs_co `mkTransKiCo` hole_co `mkTransKiCo` mkSymKiCo rhs_co
       setWantedKiCo dest co
       traceTcS "rewriteKiCoEvidence"
         $ vcat [ ppr old_ev, ppr swapped, ppr nlhs, ppr nrhs, ppr hole_co
                , ppr co, ppr new_rewriters ]
       return new_ev
  where
    new_pred = mkKiCoPred kc nlhs nrhs
    loc = ctEvLoc old_ev
    kc = fstOf3 $ getPredKis $ ctKiEvPred old_ev

{- *******************************************************************
*                                                                    *
                   tryInertEqs
*                                                                    *
******************************************************************* -}

tryInertKiCos :: KiCoCt -> SolverStage ()
tryInertKiCos work_item@(KiCoCt { kc_ev = ev }) = Stage $ do
  inerts <- getInertKiCans
  case inertsCanDischarge inerts work_item of
    Just (ev_i, swapped) -> stopWith ev "Solved from inert"
    Nothing -> continueWith ()

inertsCanDischarge :: InertKiCans -> KiCoCt -> Maybe (CtKiEvidence, SwapFlag)
inertsCanDischarge inerts (KiCoCt { kc_lhs = lhs_w, kc_rhs = rhs_w, kc_ev = ev_w })
  | (ev_i : _) <- [ ev_i | KiCoCt { kc_ev = ev_i, kc_rhs = rhs_i }
                           <- findKiCo inerts lhs_w
                         , rhs_i `tcEqMonoKind` rhs_w
                         , inert_beats_wanted ev_i ]
  = Just (ev_i, NotSwapped)

  | Just rhs_lhs <- canKiCoLHS_maybe rhs_w
  , (ev_i : _) <- [ ev_i | KiCoCt { kc_ev = ev_i, kc_rhs = rhs_i }
                           <- findKiCo inerts rhs_lhs
                         , rhs_i `tcEqMonoKind` canKiCoLHSKind lhs_w
                         , inert_beats_wanted ev_i ]
  = Just (ev_i, IsSwapped)
  where
    loc_w = ctEvLoc ev_w
    f_w = ctEvFlavor ev_w

    inert_beats_wanted ev_i
      = f_i `eqCanRewriteF` f_w
        && not ((loc_w `strictly_more_visible` ctEvLoc ev_i)
                && (f_w `eqCanRewriteF` f_i))
      where
        f_i = ctEvFlavor ev_i

    strictly_more_visible loc1 loc2
      = not (isVisibleOrigin (ctLocOrigin loc2))
        && isVisibleOrigin (ctLocOrigin loc1)

inertsCanDischarge _ _ = Nothing

{-********************************************************************
*                                                                    *
          Final wrap-up for equalities
*                                                                    *
********************************************************************-}

tryQCsIrredKiCoCt :: IrredKiCt -> SolverStage ()
tryQCsIrredKiCoCt irred@(IrredKiCt { ikr_ev = ev })
  | KiCoPred kc k1 k2 <- classifyPredKind (ctKiEvPred ev)
  = lookup_ki_co_in_qcis (CIrredCanKi irred) k1 k2
  | otherwise
  = pprPanic "solveIrredEquality" (ppr ev)

tryQCsKiCoCt :: KiCoCt -> SolverStage ()
tryQCsKiCoCt work_item@(KiCoCt { kc_lhs = lhs, kc_rhs = rhs })
  = lookup_ki_co_in_qcis (CKiCoCan work_item) (canKiCoLHSKind lhs) rhs

lookup_ki_co_in_qcis :: KiCt -> AnyMonoKind -> AnyMonoKind -> SolverStage ()
lookup_ki_co_in_qcis work_ct lhs rhs = Stage $ do
  continueWith ()
