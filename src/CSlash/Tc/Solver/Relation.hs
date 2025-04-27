module CSlash.Tc.Solver.Relation where

import CSlash.Tc.Errors.Types
import CSlash.Tc.Instance.Relation
-- import GHC.Tc.Instance.Class( safeOverlap, matchEqualityInst )
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Types.Origin
-- import GHC.Tc.Types.EvTerm( evCallStack )
import CSlash.Tc.Solver.InertSet
import CSlash.Tc.Solver.Monad
import CSlash.Tc.Solver.Types
import CSlash.Tc.Utils.TcType
-- import CSlash.Tc.Utils.Unify( uType )

import CSlash.Core
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.Predicate
-- import GHC.Core.Unify ( ruleMatchTyKiX )

import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Var
-- import GHC.Types.Id( mkTemplateLocals )
import CSlash.Types.Var.Set
import CSlash.Types.SrcLoc
import CSlash.Types.Var.Env

import CSlash.Utils.Monad ( concatMapM, foldlM )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc

import CSlash.Unit.Module

import CSlash.Data.Bag

import CSlash.Driver.DynFlags

import Data.Maybe ( listToMaybe, mapMaybe, isJust )
import Data.Void( Void )

import Control.Monad.Trans.Maybe( MaybeT, runMaybeT )
import Control.Monad.Trans.Class( lift )
import Control.Monad

solveRelNC :: CtEvidence -> KiCon -> MonoKind -> MonoKind -> SolverStage Void
solveRelNC ev kc ki1 ki2 = do
  simpleStage $ traceTcS "solveRelNC" (ppr (mkRelPred kc ki1 ki2) $$ ppr ev)
  rel_ct <- canRelCt ev kc ki1 ki2
  solveRel rel_ct

solveRel :: RelCt -> SolverStage Void
solveRel rel_ct@(RelCt { rl_ev = ev, rl_kc = kc, rl_ki1 = ki1, rl_ki2 = ki2 })
  | isEqualityKiCon kc
  = panic "solveRel"
  | otherwise
  = do simpleStage $ traceTcS "solveRel" (panic "ppr rel_ct")
       tryInertRels rel_ct
       tryInstances rel_ct
       panic "unfinished"

canRelCt :: CtEvidence -> KiCon -> MonoKind -> MonoKind -> SolverStage RelCt
canRelCt ev kc ki1 ki2
  | isGiven ev
  = panic "canRelCt"
  | otherwise
  = Stage $ continueWith $ RelCt { rl_ev = ev, rl_kc = kc, rl_ki1 = ki1, rl_ki2 = ki2 }
      
{- ******************************************************************************
*                                                                               *
                   interactRel
*                                                                               *
****************************************************************************** -}

tryInertRels :: RelCt -> SolverStage ()
tryInertRels rel_ct = Stage $ do
  inerts <- getInertCans
  try_inert_rels inerts rel_ct

try_inert_rels :: InertCans -> RelCt -> TcS (StopOrContinue ())
try_inert_rels inerts rel_w@(RelCt { rl_ev = ev_w, rl_kc = kc, rl_ki1 = ki1, rl_ki2 = ki2 })
  | Just rel_i <- lookupInertRel inerts (ctEvLoc ev_w) kc ki1 ki2
  , let ev_i = relCtEvidence rel_i
        loc_i = ctEvLoc ev_i
        loc_w = ctEvLoc ev_w
  = do dflags <- getDynFlags
       short_cut_worked <- shortCutSolver ev_w ev_i
       if short_cut_worked
         then stopWith ev_w "interactRel/solved from rel"
         else panic "try_inert_rels"
  | otherwise
  = do panic "traceTcS "--tryInertRels:no" (ppr rel_w $$ ppr kc <+> ppr ki1 <+> ppr ki2)
       continueWith ()

shortCutSolver :: CtEvidence -> CtEvidence -> TcS Bool
shortCutSolver ev_w ev_i
  | isWanted ev_w
  , isGiven ev_i
  = panic "shortCutSolver"
  | otherwise
  = return False

{- *******************************************************************
*                                                                    *
         Top-level reaction for rel constraints (CRelCan)
*                                                                    *
**********************************************************************-}

tryInstances :: RelCt -> SolverStage ()
tryInstances rel_ct = Stage $ do
  inerts <- getInertSet
  try_instances inerts rel_ct

try_instances :: InertSet -> RelCt -> TcS (StopOrContinue ())
try_instances inerts work_item@(RelCt { rl_ev = ev, rl_kc = kc, rl_ki1 = ki1, rl_ki2 = ki2 })
  | isGiven ev
  = continueWith ()
  | Just solved_ev <- lookupSolvedRel inerts rel_loc kc ki1 ki2
  = do panic "setEvBindIfWanted ev True (ctEvTerm solved_ev)"
       stopWith ev "Rel/Top (cached)"
  | otherwise
  = do dflags <- getDynFlags
       lkup_res <- matchRelInst dflags inerts kc ki1 ki2 rel_loc
       case lkup_res of
         OneInst { rir_what = what }
           -> do updSolvedRels what work_item
                 chooseInstance ev lkup_res
         _ -> continueWith ()
  where
    rel_loc = ctEvLoc ev

chooseInstance :: CtEvidence -> RelInstResult -> TcS (StopOrContinue a)
chooseInstance work_item (OneInst { rir_new_theta = theta
                                  , rir_what = what
                                  , rir_canonical = canonical })
  = do traceTcS "doTopReact/found instance for " $ ppr work_item
       deeper_loc <- checkInstanceOK loc what pred
       panic "checkReductionDepth deeper_loc pred"
       panic "assertPprM (getTcKiEvBindsVar >>= return . not . isCoE"
  where
    pred = ctEvPred work_item
    loc = ctEvLoc work_item

chooseInstance work_item lookup_res = pprPanic "chooseInstance" (ppr work_item $$ panic "ppr lookup_res")

checkInstanceOK :: CtLoc -> InstanceWhat -> TcPredKind -> TcS CtLoc
checkInstanceOK loc what pred = panic "checkInstanceOK"

matchRelInst
  :: DynFlags
  -> InertSet
  -> KiCon
  -> MonoKind
  -> MonoKind
  -> CtLoc
  -> TcS RelInstResult
matchRelInst dflags inerts kc k1 k2 loc = panic "matchRelInst"
