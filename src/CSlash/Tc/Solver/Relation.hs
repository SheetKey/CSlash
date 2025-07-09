module CSlash.Tc.Solver.Relation where

import CSlash.Tc.Errors.Types
-- import CSlash.Tc.Instance.Relation (RelInstResult(..))
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

-- solveRelNC :: CtEvidence -> KiCon -> AnyMonoKind -> AnyMonoKind -> SolverStage Void
-- solveRelNC ev kc ki1 ki2 = do
--   simpleStage $ traceTcS "solveRelNC" (ppr (mkRelPred kc ki1 ki2) $$ ppr ev)
--   rel_ct <- canRelCt ev kc ki1 ki2
--   solveRel rel_ct

-- solveRel :: RelCt -> SolverStage Void
-- solveRel rel_ct@(RelCt { rl_ev = ev, rl_kc = kc, rl_ki1 = ki1, rl_ki2 = ki2 })
--   | isEqualityKiCon kc
--   = panic "solveRel"
--   | otherwise
--   = do simpleStage $ traceTcS "solveRel" (ppr rel_ct)
--        tryInertRels rel_ct
--        tryInstances rel_ct

--        simpleStage (updInertRels rel_ct)
--        stopWithStage (relCtEvidence rel_ct) "Kept inert RelCt"

-- updInertRels :: RelCt -> TcS ()
-- updInertRels rel_ct@(RelCt { rl_kc = kc, rl_ev = ev, rl_ki1 = k1, rl_ki2 = k2 }) = do
--   traceTcS "Adding inert rel" (ppr rel_ct $$ ppr kc <+> ppr [k1, k2])
--   updInertCans (updRels (addRel rel_ct))

-- canRelCt :: CtEvidence -> KiCon -> AnyMonoKind -> AnyMonoKind -> SolverStage RelCt
-- canRelCt ev kc ki1 ki2
--   | isGiven ev
--   = Stage $ continueWith $ RelCt { rl_ev = ev, rl_kc = kc, rl_ki1 = ki1, rl_ki2 = ki2 }
--   | otherwise
--   = Stage $ continueWith $ RelCt { rl_ev = ev, rl_kc = kc, rl_ki1 = ki1, rl_ki2 = ki2 }
      
-- {- ******************************************************************************
-- *                                                                               *
--                    interactRel
-- *                                                                               *
-- ****************************************************************************** -}

-- tryInertRels :: RelCt -> SolverStage ()
-- tryInertRels rel_ct = Stage $ do
--   inerts <- getInertCans
--   try_inert_rels inerts rel_ct

-- try_inert_rels :: InertCans -> RelCt -> TcS (StopOrContinue ())
-- try_inert_rels inerts rel_w@(RelCt { rl_ev = ev_w, rl_kc = kc, rl_ki1 = ki1, rl_ki2 = ki2 })
--   | Just rel_i <- lookupInertRel inerts (ctEvLoc ev_w) kc ki1 ki2
--   , let ev_i = relCtEvidence rel_i
--         loc_i = ctEvLoc ev_i
--         loc_w = ctEvLoc ev_w
--   = do dflags <- getDynFlags
--        short_cut_worked <- shortCutSolver dflags ev_w ev_i
--        if short_cut_worked
--          then stopWith ev_w "interactRel/solved from rel"
--          else case solveOneFromTheOther (CRelCan rel_i) (CRelCan rel_w) of
--                 KeepInert -> do traceTcS "lookupInertRel:KeepInert" (ppr rel_w)
--                                 setKiEvBindIfWanted ev_w True (ctEvType ev_i)
--                                 return $ Stop ev_w (text "Rel equal" <+> ppr rel_w)
--                 KeepWork -> do traceTcS "lookupInertRel:KeepWork" (ppr rel_w)
--                                setKiEvBindIfWanted ev_i True (ctEvType ev_w)
--                                updInertCans (updRels $ delRel rel_w)
--                                continueWith ()
--   | otherwise
--   = do traceTcS "tryInertRels:no" (ppr rel_w $$ ppr kc <+> ppr ki1 <+> ppr ki2)
--        continueWith ()

-- shortCutSolver :: DynFlags -> CtEvidence -> CtEvidence -> TcS Bool
-- shortCutSolver dflags ev_w ev_i
--   | isWanted ev_w
--   , isGiven ev_i
--   = do ev_binds_var <- getTcKiEvBindsVar
--        ev_binds <- getTcKiEvBindsMap ev_binds_var
--        solved_rels <- getSolvedRels
--        mb_stuff <- try_solve_from_instance solved_rels ev_w
--        case mb_stuff of
--          Nothing -> return False
--          Just solved_rels' -> do
--            setSolvedRels solved_rels'
--            return True
--   | otherwise
--   = return False
--   where
--     loc_w = ctEvLoc ev_w

--     try_solve_from_instance :: RelMap RelCt -> CtEvidence -> TcS (Maybe (RelMap RelCt))
--     try_solve_from_instance solved_rels ev
--       | let pred = ctEvPred ev
--       , RelPred rl k1 k2 <- classifyPredKind pred
--       = do inst_res <- matchGlobalInst dflags True rl k1 k2 loc_w
--            case inst_res of
--              OneInst { rir_canonical = canonical, rir_what = what } -> do
--                let rel_ct = RelCt { rl_ev = ev, rl_kc = rl, rl_ki1 = k1, rl_ki2 = k2 }
--                    solved_rels' = addSolvedRel rel_ct solved_rels
--                traceTcS "shortCutSolver: found instnace" empty
--                loc' <- checkInstanceOK (ctEvLoc ev) what pred
--                checkReductionDepth loc' pred
--                return $ Just solved_rels'
--              _ -> return Nothing
--       | otherwise
--       = return Nothing

-- {- *******************************************************************
-- *                                                                    *
--          Top-level reaction for rel constraints (CRelCan)
-- *                                                                    *
-- **********************************************************************-}

-- tryInstances :: RelCt -> SolverStage ()
-- tryInstances rel_ct = Stage $ do
--   inerts <- getInertSet
--   try_instances inerts rel_ct

-- try_instances :: InertSet -> RelCt -> TcS (StopOrContinue ())
-- try_instances inerts work_item@(RelCt { rl_ev = ev, rl_kc = kc, rl_ki1 = ki1, rl_ki2 = ki2 })
--   | isGiven ev
--   = continueWith ()
--   | Just solved_ev <- lookupSolvedRel inerts rel_loc kc ki1 ki2
--   = do setKiEvBindIfWanted ev True (ctEvType solved_ev)
--        stopWith ev "Rel/Top (cached)"
--   | otherwise
--   = do dflags <- getDynFlags
--        lkup_res <- matchRelInst dflags inerts kc ki1 ki2 rel_loc
--        case lkup_res of
--          OneInst { rir_what = what }
--            -> do updSolvedRels what work_item
--                  chooseInstance ev lkup_res
--          _ -> continueWith ()
--   where
--     rel_loc = ctEvLoc ev

-- chooseInstance :: CtEvidence -> RelInstResult -> TcS (StopOrContinue a)
-- chooseInstance work_item (OneInst { rir_what = what
--                                   , rir_ev = ev
--                                   , rir_canonical = canonical })
--   = do traceTcS "doTopReact/found instance for " $ ppr work_item
--        deeper_loc <- checkInstanceOK loc what pred
--        checkReductionDepth deeper_loc pred
--        setKiEvBindIfWanted work_item canonical ev
--        stopWith work_item "Rel/Top (solved wanted)"
--   where
--     pred = ctEvPred work_item
--     loc = ctEvLoc work_item

-- chooseInstance work_item lookup_res = pprPanic "chooseInstance" (ppr work_item $$ ppr lookup_res)

-- checkInstanceOK :: CtLoc -> InstanceWhat -> AnyPredKind -> TcS CtLoc
-- checkInstanceOK loc what pred = return deeper_loc
--   where
--     deeper_loc = bumpCtLocDepth loc

-- matchRelInst
--   :: DynFlags
--   -> InertSet
--   -> KiCon
--   -> AnyMonoKind
--   -> AnyMonoKind
--   -> CtLoc
--   -> TcS RelInstResult
-- matchRelInst dflags inerts kc k1 k2 loc
--   | not (noMatchableGivenRels inerts loc kc k1 k2)
--   = do traceTcS "Delaying instance application"
--          $ vcat [ text "Work item:" <+> ppr (mkKiConApp kc [k1, k2]) ]
--        return NotSure
--   | otherwise
--   = do traceTcS "matchRelInst" $ text "pred =" <+> ppr kc <+> char '{'
--        local_res <- matchLocalInst kc k1 k2 loc
--        case local_res of
--          OneInst {} -> do traceTcS "} matchRelInst local match" $ ppr local_res
--                           return local_res
--          NotSure -> do traceTcS "} matchRelInst local not sure" empty
--                        return local_res
--          NoInstance -> do global_res <- matchGlobalInst dflags False kc k1 k2 loc
--                           traceTcS "} matchRelInst global result" $ ppr global_res
--                           return global_res

-- matchLocalInst :: KiCon -> AnyMonoKind -> AnyMonoKind -> CtLoc -> TcS RelInstResult
-- matchLocalInst kc k1 k2 loc = do
--   --inerts@(IS { inert_cans = ics }) <- getInertSet
--   traceTcS "SKIPPING match_local_inst SINCE THERE IS NOT 'QCInst' OR 'inert_insts'" empty
--   traceTcS "No local instance for" (ppr (mkKiConApp kc [k1, k2]))
--   return NoInstance
