module CSlash.Tc.Solver.Equality (solveKiEquality) where

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

solveKiEquality :: CtEvidence -> AnyMonoKind -> AnyMonoKind -> SolverStage Void
solveKiEquality ev ki1 ki2 = do
  Pair ki1' ki2' <- zonkEqKinds ev ki1 ki2
  let ev' | debugIsOn = setCtEvPredKind ev $ mkKiEqPred ki1' ki2'
          | otherwise = ev

  mb_canon <- canonicalizeKiEquality ev' ki1' ki2'

  case mb_canon of
    Left irred_ct -> do tryQCsIrredEqCt irred_ct
                        solveIrred irred_ct
    Right eq_ct -> do tryInertEqs eq_ct
                      tryQCsEqCt eq_ct
                      simpleStage (updInertEqs eq_ct)
                      stopWithStage (eqCtEvidence eq_ct) "Kept inert EqCt"

updInertEqs :: EqCt -> TcS ()
updInertEqs eq_ct = do
  kickOutRewritable (KOAfterAdding (eqCtLHS eq_ct)) (eqCtFlavor eq_ct)
  tc_lvl <- getTcLevel
  updInertCans (addEqToCans tc_lvl eq_ct)

{- *********************************************************************
*                                                                      *
*           zonkEqKinds
*                                                                      *
********************************************************************* -}

zonkEqKinds :: CtEvidence -> AnyMonoKind -> AnyMonoKind -> SolverStage (Pair AnyMonoKind)
zonkEqKinds ev ki1 ki2 = Stage $ do
  res <- go_mono ki1 ki2
  case res of
    Left pair -> continueWith pair
    Right ki -> canKiEqReflexive ev ki
  where
    go_mono :: AnyMonoKind -> AnyMonoKind -> TcS (Either (Pair AnyMonoKind) AnyMonoKind)
    go_mono ki1@(KiConApp kc1 kis1) (KiConApp kc2 kis2)
      = if kc1 == kc2 && kis1 `equalLength` kis2
        then kicon kc1 kis1 kis2
        else bale_out ki1 ki2
    go_mono (KiVarKi kv1) (KiVarKi kv2) = kivar_kivar kv1 kv2
    go_mono (KiVarKi kv1) ki2 = kivar NotSwapped kv1 ki2
    go_mono ki1 (KiVarKi kv2) = kivar IsSwapped kv2 ki1

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

    kicon
      :: KiCon
      -> [AnyMonoKind]
      -> [AnyMonoKind]
      -> TcS (Either (Pair AnyMonoKind) AnyMonoKind)
    kicon kc kis1 kis2 = do
      results <- zipWithM go_mono kis1 kis2
      return $ case combine_results results of
                 Left kis -> Left $ mkKiConApp kc <$> kis
                 Right kis -> Right $ mkKiConApp kc kis

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
*           canonicaliseKiEquality
*                                                                      *
********************************************************************* -}

canonicalizeKiEquality :: CtEvidence -> AnyMonoKind -> AnyMonoKind -> SolverStage (Either IrredCt EqCt)
canonicalizeKiEquality ev ki1 ki2 = Stage $ do
  traceTcS "canonicalizeKiEquality"
    $ vcat [ ppr ev, ppr ki1, ppr ki2 ]
  rdr_env <- getGlobalRdrEnvTcS
  can_ki_eq_nc False rdr_env ev ki1 ki2

can_ki_eq_nc
  :: Bool
  -> GlobalRdrEnv
  -> CtEvidence
  -> AnyMonoKind
  -> AnyMonoKind
  -> TcS (StopOrContinue (Either IrredCt EqCt))

can_ki_eq_nc _ _ ev ki1@(KiConApp kc1 []) (KiConApp kc2 []) 
  | kc1 == kc2
  = panic "canKiEqReflexive ev ki1"

can_ki_eq_nc True _ ev ki1 ki2
  | ki1 `tcEqMonoKind` ki2
  = panic "canKiEqReflexive ev ki1"

----------------------
-- Otherwise try to decompose
----------------------

can_ki_eq_nc _ _ ev (FunKi f1 ki1a ki1b) (FunKi f2 ki2a ki2b)
  | f1 == f2
  = canDecomposableFunKi ev f1 (ki1a, ki1b) (ki2a, ki2b)

can_ki_eq_nc _ _ ev (KiConApp kc1 kis1) (KiConApp kc2 kis2)
  = panic "canKiConApp ev kc1 kis1 kc2 kis2"

------------------
-- Can't decompose
------------------

can_ki_eq_nc False rdr_env ev ps_ki1 ps_ki2 = do
  (redn1@(ReductionKi _ xi1), rewriters1) <- panic "rewriteKi ev ps_ki1"
  (redn2@(ReductionKi _ xi2), rewriters2) <- panic "rewriteKi ev ps_ki2"
  new_ev <- rewriteKiEqEvidence (rewriters1 S.<> rewriters2) ev NotSwapped redn1 redn2
  traceTcS "can_ki_eq_nc: go round again" (panic "ppr new_ev $$ ppr xi1 $$ ppr xi2")
  panic "can_ki_eq_nc True rdr_env new_ev xi1 xi2 "

can_ki_eq_nc True _ ev ki1 ki2
  | Just can_eq_lhs1 <- canKiEqLHS_maybe ki1
  = do traceTcS "can_ki_eq1" (ppr ki1 $$ ppr ki2)
       panic "canKiEqCanLHSHomo ev NotSwapped can_eq_lhs1 ki1 ki2 ki2"

  | Just can_eq_lhs2 <- canKiEqLHS_maybe ki2
  = do traceTcS "can_ki_eq2" (ppr ki1 $$ ppr ki2)
       panic "canKiEqCanLHSHomo ev IsSwapped can_eq_lhs2 ki2 ki1 ki1"

------------------
-- Failed
------------------

can_ki_eq_nc True _ ev ps_ki1 ps_ki2 = do
  traceTcS "can_ki_eq_nc catch-all case" (ppr ps_ki1 $$ ppr ps_ki2)
  finishCanWithIrred ShapeMismatchReason ev

canKiConApp
  :: CtEvidence
  -> KiCon
  -> [TcMonoKind]
  -> KiCon
  -> [TcMonoKind]
  -> TcS (StopOrContinue (Either IrredCt EqCt))
canKiConApp ev kc1 kis1 kc2 kis2
  | kc1 == kc2
  , kis1 `equalLength` kis2
  = canDecomposableKiConAppOK ev kc1 kis1 kis2
  | otherwise
  = canKiEqHardFailure ev ki1 ki2
  where
    ki1 = mkKiConApp kc1 kis1
    ki2 = mkKiConApp kc2 kis2

canDecomposableKiConAppOK
  :: CtEvidence
  -> KiCon
  -> [TcMonoKind]
  -> [TcMonoKind]
  -> TcS (StopOrContinue a)
canDecomposableKiConAppOK ev kc kis1 kis2 = assert (kis1 `equalLength` kis2) $ do
  traceTcS "canDecomposableKiConAppOK"
    (ppr ev $$ ppr kc $$ ppr kis1 $$ ppr kis2)
  case ev of
    CtWanted { ctev_dest = dest } -> do
      (co, _, _) <- wrapUnifierTcS ev $ \uenv -> do
        cos <- panic "zipWithM (u_arg uenv) kis1 kis2"
        return $ mkKiConAppCo kc cos
      setWantedEq dest co
    CtGiven { ctev_evar = evar } -> pprPanic "canDecomposableKiConAppOK/CtGiven"
                                    $ vcat [ ppr ev, ppr kc, ppr kis1, ppr kis2 ]
  stopWith ev "Decomposed KiConApp"
  where
    loc = ctEvLoc ev

    u_arg uenv = uKind arg_env
      where arg_env = uenv `updUEnvLoc` const arg_loc

    arg_loc = adjustCtLoc True True loc      

canDecomposableFunKi
  :: CtEvidence
  -> FunKiFlag
  -> (AnyMonoKind, AnyMonoKind)
  -> (AnyMonoKind, AnyMonoKind)
  -> TcS (StopOrContinue a)
canDecomposableFunKi ev f f1@(a1, r1) f2@(a2, r2) = do
  traceTcS "canDecomposableFunKi"
    $ ppr ev $$ ppr f1 $$ ppr f2
  case ev of
    CtWanted { ctev_dest = dest } -> do
      (co, _, _) <- wrapUnifierTcS ev $ \uenv -> do
        arg <- uKind uenv a1 a2
        res <- uKind uenv r1 r2
        return $ mkFunKiCo f arg res
      setWantedEq dest co
    CtGiven { ctev_evar = evar } -> pprPanic "canDecomposableFunKi"
                                    $ vcat [ ppr ev, ppr f1, ppr f2 ]
  stopWith ev "Decomposed FunKi"

canKiEqHardFailure
  :: CtEvidence
  -> TcMonoKind
  -> TcMonoKind
  -> TcS (StopOrContinue (Either IrredCt a))
canKiEqHardFailure ev ki1 ki2 = do
  traceTcS "canKiEqHardFailure" (ppr ki1 $$ ppr ki2)
  (redn1, rewriters1) <- rewriteKiForErrors ev ki1
  (redn2, rewriters2) <- rewriteKiForErrors ev ki2
  new_ev <- rewriteKiEqEvidence (rewriters1 S.<> rewriters2) ev NotSwapped redn1 redn2
  finishCanWithIrred ShapeMismatchReason new_ev

canKiEqCanLHSHomo
  :: CtEvidence
  -> SwapFlag
  -> CanEqLHS
  -> TcMonoKind
  -> TcMonoKind
  -> TcMonoKind
  -> TcS (StopOrContinue (Either IrredCt EqCt))
canKiEqCanLHSHomo ev swapped lhs1 ps_xi1 xi2 ps_xi2
  | Just lhs2 <- panic "canKiEqLHS_maybe xi2"
  = canKiEqCanLHS2 ev swapped lhs1 ps_xi1 lhs2 ps_xi2
  | otherwise
  = canKiEqCanLHSFinish ev swapped lhs1 ps_xi2

canKiEqCanLHS2
  :: CtEvidence
  -> SwapFlag
  -> CanEqLHS
  -> TcMonoKind
  -> CanEqLHS
  -> TcMonoKind
  -> TcS (StopOrContinue (Either IrredCt EqCt))
canKiEqCanLHS2 ev swapped lhs1 ps_xi1 lhs2 ps_xi2
  | lhs1 `eqCanEqLHS` lhs2
  = panic "canKiEqReflexive ev lhs1_ki"
  | KiVarLHS kv1 <- lhs1
  , KiVarLHS kv2 <- lhs2
  = do traceTcS "canEqLHS2 swapOver" (ppr kv1 $$ ppr kv2 $$ ppr swapped)
       if panic "swapOverKiVars (isGiven ev) kv1 kv2"
         then finish_with_swapping
         else finish_without_swapping

  where
    lhs1_ki = canKiEqLHSKind lhs1
    lhs2_ki = canKiEqLHSKind lhs2

    finish_without_swapping = canKiEqCanLHSFinish ev swapped lhs1 ps_xi2

    finish_with_swapping = do
      new_ev <- rewriteKiEqEvidence
                emptyRewriterSet ev swapped (panic "mkReflRednKi lhs1_ki") (panic "mkReflRednKi lhs2_ki")
      canKiEqCanLHSFinish new_ev IsSwapped lhs2 ps_xi1

canKiEqCanLHSFinish
  :: CtEvidence
  -> SwapFlag
  -> CanEqLHS
  -> TcMonoKind
  -> TcS (StopOrContinue (Either IrredCt EqCt))
canKiEqCanLHSFinish ev swapped lhs rhs = do
  traceTcS "canKiEqCanLHSFinish"
    $ vcat [ text "ev:" <+> ppr ev
           , text "swapped:" <+> ppr swapped
           , text "lhs:" <+> ppr lhs
           , text "rhs:" <+> ppr rhs ]

  canKiEqCanLHSFinish_try_unification ev swapped lhs rhs

canKiEqCanLHSFinish_try_unification
  :: CtEvidence
  -> SwapFlag
  -> CanEqLHS
  -> TcMonoKind
  -> TcS (StopOrContinue (Either IrredCt EqCt))
canKiEqCanLHSFinish_try_unification ev swapped lhs rhs
  | isWanted ev
  , KiVarLHS kv <- lhs
  = do given_eq_lvl <- getInnermostGivenEqLevel
       if not (panic "touchabilityAndShapeTestKind given_eq_lvl kv rhs")
         then canKiEqCanLHSFinish_no_unification ev swapped lhs rhs
         else
         do check_result <- panic "checkTouchableKiVarEq ev kv rhs"
            case check_result of
              PuFail reason
                | reason `ctkerHasOnlyProblems` do_not_prevent_rewriting
                -> canKiEqCanLHSFinish_no_unification ev swapped lhs rhs
                | otherwise
                -> tryIrredInstead reason ev swapped lhs rhs
              PuOK _ rhs_redn ->
                do let kv_ki = panic "mkKiVarKi kv"
                   new_ev <- if isReflKiCo (reductionKindCoercion rhs_redn)
                             then return ev
                             else rewriteKiEqEvidence emptyRewriterSet
                                    ev swapped (panic "mkReflRednKi kv_ki") rhs_redn
                   let final_rhs = reductionReducedKind rhs_redn

                   traceTcS "Sneaky unification:"
                     $ text "Unifies:" <+> ppr kv <+> text ":=" <+> ppr final_rhs

                   panic "unifyKiVar kv final_rhs"

                   panic "kickOutAfterUnification [kv]"

                   return $ Stop new_ev (text "Solved by unification")
  | otherwise
  = canKiEqCanLHSFinish_no_unification ev swapped lhs rhs
  where
    do_not_prevent_rewriting = ctkeProblem ctkeSkolemEscape S.<> ctkeProblem ctkeConcrete

canKiEqCanLHSFinish_no_unification
  :: CtEvidence
  -> SwapFlag
  -> CanEqLHS
  -> TcMonoKind
  -> TcS (StopOrContinue (Either IrredCt EqCt))
canKiEqCanLHSFinish_no_unification ev swapped lhs rhs = do
  check_result <- checkKindEq ev lhs rhs
  case check_result of
    PuFail reason -> tryIrredInstead reason ev swapped lhs rhs
    PuOK _ rhs_redn -> do
      let lhs_ki = canKiEqLHSKind lhs
      new_ev <- rewriteKiEqEvidence emptyRewriterSet ev swapped (panic "mkReflRednKi lhs_ki") rhs_redn
      continueWith $ Right $ KiEqCt { eq_ev = new_ev
                                  , eq_lhs = lhs
                                  , eq_rhs = panic "reductionReducedKind rhs_redn" }

tryIrredInstead
  :: CheckTyKiEqResult
  -> CtEvidence
  -> SwapFlag
  -> CanEqLHS
  -> TcMonoKind
  -> TcS (StopOrContinue (Either IrredCt a))
tryIrredInstead reason ev swapped lhs rhs = do
  traceTcS "cantMakeCaconical" (ppr reason $$ ppr lhs $$ ppr rhs)
  new_ev <- rewriteKiEqEvidence
            emptyRewriterSet ev swapped (panic "mkReflRednKi $ canKiEqLHSKind lhs") (panic "mkReflRednKi rhs")
  finishCanWithIrred (NonCanonicalReason reason) new_ev

finishCanWithIrred :: CtIrredReason -> CtEvidence -> TcS (StopOrContinue (Either IrredCt a))
finishCanWithIrred reason ev = do
  when (isInsolubleReason reason) tryEarlyAbortTcS
  continueWith $ Left $ IrredCt { ir_ev = ev, ir_reason = reason }

canKiEqReflexive :: CtEvidence -> AnyMonoKind -> TcS (StopOrContinue a)
canKiEqReflexive ev ki = do
  setKiEvBindIfWanted ev True
    $ kiEvCoercion (mkReflKiCo ki)
  stopWith ev "Solved by reflexivity"

{- *******************************************************************
*                                                                    *
                   Rewriting evidence
*                                                                    *
******************************************************************* -}

rewriteKiEqEvidence
  :: RewriterSet
  -> CtEvidence
  -> SwapFlag
  -> Reduction
  -> Reduction
  -> TcS CtEvidence
rewriteKiEqEvidence new_rewriters old_ev swapped (ReductionKi lhs_co nlhs) (ReductionKi rhs_co nrhs)
  | NotSwapped <- swapped
  , isReflKiCo lhs_co
  , isReflKiCo rhs_co
  = return $ panic "setCtEvPredKind old_ev new_pred"
  | CtGiven { ctev_evar = old_evar } <- old_ev
  = panic "rewriteKiEqEvidence"
  | CtWanted { ctev_dest = dest, ctev_rewriters = rewriters } <- old_ev
  , let rewriters' = rewriters S.<> new_rewriters
  = do (new_ev, hole_co) <- panic "newWantedKiEq loc rewriters' nlhs nrhs"
       let co = panic "maybeSymCo swapped $ lhs_co `mkTransKiCo` hole_co `mkTransKiCo` mkSymKiCo rhs_co"
       setWantedEq dest co
       traceTcS "rewriterEqEvidence"
         $ vcat [ panic "ppr old_ev, ppr nlhs, ppr nrhs, ppr co, ppr new_rewriters" ]
       return new_ev
  where
    new_pred = mkKiEqPred nlhs nrhs
    loc = ctEvLoc old_ev

{- *******************************************************************
*                                                                    *
                   tryInertEqs
*                                                                    *
******************************************************************* -}

tryInertEqs :: EqCt -> SolverStage ()
tryInertEqs work_item@(KiEqCt { eq_ev = ev }) = Stage $ do
  inerts <- getInertCans
  case inertsCanDischarge inerts work_item of
    Just (ev_i, swapped) -> stopWith ev "Solved from inert"
    Nothing -> continueWith ()

inertsCanDischarge :: InertCans -> EqCt -> Maybe (CtEvidence, SwapFlag)
inertsCanDischarge inerts (KiEqCt { eq_lhs = lhs_w, eq_rhs = rhs_w, eq_ev = ev_w })
  | (ev_i : _) <- [ ev_i | KiEqCt { eq_ev = ev_i, eq_rhs = rhs_i }
                           <- findEq inerts lhs_w
                         , rhs_i `tcEqMonoKind` rhs_w
                         , inert_beats_wanted ev_i ]
  = Just (ev_i, NotSwapped)

  | Just rhs_lhs <- canKiEqLHS_maybe rhs_w
  , (ev_i : _) <- [ ev_i | KiEqCt { eq_ev = ev_i, eq_rhs = rhs_i }
                           <- findEq inerts rhs_lhs
                         , rhs_i `tcEqMonoKind` canKiEqLHSKind lhs_w
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

tryQCsIrredEqCt :: IrredCt -> SolverStage ()
tryQCsIrredEqCt irred@(IrredCt { ir_ev = ev })
  | EqPred k1 k2 <- classifyPredKind (ctEvPred ev)
  = panic "lookup_ki_eq_in_qcis (CIrredCan irred) k1 k2"
  | otherwise
  = pprPanic "solveIrredEquality" (ppr ev)

tryQCsEqCt :: EqCt -> SolverStage ()
tryQCsEqCt work_item@(KiEqCt { eq_lhs = lhs, eq_rhs = rhs })
  = lookup_ki_eq_in_qcis (CEqCan work_item) (panic "canKiEqLHSKind lhs") (panic "rhs")

lookup_ki_eq_in_qcis :: Ct -> TcMonoKind -> TcMonoKind -> SolverStage ()
lookup_ki_eq_in_qcis work_ct lhs rhs = Stage $ do
  continueWith ()
