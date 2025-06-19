{-# LANGUAGE TupleSections #-}

module CSlash.Tc.Solver where

import Prelude hiding ((<>))

import CSlash.Data.Bag
-- import GHC.Core.Class
import CSlash.Core
import CSlash.Core.DataCon
-- import GHC.Core.Make
import CSlash.Driver.DynFlags
import CSlash.Data.FastString
import CSlash.Data.List.SetOps
import CSlash.Types.Name
import CSlash.Types.Unique.Set
import CSlash.Types.Id
import CSlash.Utils.Outputable
import CSlash.Builtin.Utils
import CSlash.Builtin.Names
import CSlash.Tc.Errors
import CSlash.Tc.Errors.Types
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Solver.Solve ( solveSimpleGivens, solveSimpleWanteds )
-- import GHC.Tc.Solver.Dict    ( makeSuperClasses, solveCallStack )
-- import GHC.Tc.Solver.Rewrite ( rewriteType )
import CSlash.Tc.Utils.Unify    ( buildVImplication )
-- import GHC.Tc.Utils.TcMType as TcM
import CSlash.Tc.Utils.Monad as TcM
import CSlash.Tc.Zonk.TcType as TcM
import CSlash.Tc.Solver.InertSet
import CSlash.Tc.Solver.Monad as TcS
import CSlash.Tc.Types.Constraint
-- import GHC.Tc.Instance.FunDeps
-- import GHC.Core.Predicate
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.TcType
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.Ppr
-- import CSlash.Core.TyCon    ( TyConBinder{-, isTypeFamilyTyCon-} )
import CSlash.Builtin.Types
-- import GHC.Core.Unify    ( tcMatchTyKis )
import CSlash.Unit.Module ( getModule )
import CSlash.Utils.Misc
import CSlash.Utils.Panic
-- import CSlash.Types.TyThing ( MonadThings(lookupId) )
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Basic
-- import CSlash.Types.Id.Make  ( unboxedUnitExpr )
import CSlash.Types.Error

import Control.Monad
import Control.Monad.Trans.Class        ( lift )
import Control.Monad.Trans.State.Strict ( StateT(runStateT), put )
import Data.Foldable      ( toList, traverse_ )
import Data.List          ( partition )
import Data.List.NonEmpty ( NonEmpty(..), nonEmpty )
import qualified Data.List.NonEmpty as NE
import CSlash.Data.Maybe     ( mapMaybe, runMaybeT, MaybeT )

{- ******************************************************************************
*                                                                               *
*                           External interface                                  *
*                                                                               *
****************************************************************************** -}

captureTopConstraints :: TcM a -> TcM (a, WantedConstraints)
captureTopConstraints thing_inside = do
  static_wc_var <- TcM.newTcRef emptyWC
  (mb_res, lie) <- TcM.updGblEnv (\env -> env { tcg_static_wc = static_wc_var })
                                 $ TcM.tryCaptureConstraints thing_inside
  stWC <- TcM.readTcRef static_wc_var
  case mb_res of
    Just res -> return (res, lie `andWC` stWC)
    Nothing -> do _ <- simplifyTop lie
                  failM

simplifyTop :: WantedConstraints -> TcM (Bag KiEvBind)
simplifyTop wanteds = do
  traceTc "simplifyTop {" $ text "wanted = " <+> ppr wanteds
  (final_wc, binds1) <- runTcS $ simplifyTopWanteds wanteds
  traceTc "End simplifyTop }" empty

  binds2 <- reportUnsolved final_wc

  return (kiEvBindMapBinds binds1 `unionBags` binds2)

pushLevelAndSolveEqualities :: SkolemInfoAnon -> [TcKiVar] -> TcM a -> TcM a
pushLevelAndSolveEqualities skol_info_anon tcbs thing_inside = do
  (tclvl, wanted, res) <- pushLevelAndSolveEqualitiesX "pushLevelAndSolveEqualities" thing_inside
  report_unsolved_equalities skol_info_anon tcbs tclvl wanted
  return res

pushLevelAndSolveEqualitiesX :: String -> TcM a -> TcM (TcLevel, WantedConstraints, a)
pushLevelAndSolveEqualitiesX callsite thing_inside = do
  traceTc "pushLevelAndSolveEqualitiesX {" (text "Called from" <+> text callsite)
  (tclvl, (wanted, res)) <- pushTcLevelM $ do
    (res, wanted) <- captureConstraints thing_inside
    wanted <- runTcSEqualities (simplifyTopWanteds wanted)
    return (wanted, res)
  traceTc "pushLevelAndSolveEqualities }" (vcat [ text "Residual:" <+> ppr wanted
                                                , text "Level:" <+> ppr tclvl ])
  return (tclvl, wanted, res)

report_unsolved_equalities
  :: SkolemInfoAnon -> [TcKiVar] -> TcLevel -> WantedConstraints -> TcM ()
report_unsolved_equalities skol_info_anon skol_vs tclvl wanted
  | isEmptyWC wanted
  = return ()
  | otherwise
  = checkNoErrs $ do
      implic <- buildVImplication skol_info_anon skol_vs tclvl wanted
      reportAllUnsolved (mkImplicWC (unitBag implic))

simplifyTopWanteds :: WantedConstraints -> TcS WantedConstraints
simplifyTopWanteds wanteds = do
  wc_first_go <- nestTcS (solveWanteds wanteds)
  useUnsatisfiableGivens wc_first_go

useUnsatisfiableGivens :: WantedConstraints -> TcS WantedConstraints
useUnsatisfiableGivens wc = do
  (final_wc, did_work) <- (`runStateT` False) $ go_wc wc
  if did_work
    then nestTcS (solveWanteds final_wc)
    else return final_wc
  where
    go_wc (WC { wc_simple = wtds, wc_impl = impls }) = do
      impls' <- mapMaybeBagM go_impl impls
      return $ WC { wc_simple = wtds, wc_impl = impls' }

    go_impl impl
      | isSolvedStatus (ic_status impl)
      = return $ Just impl
      | otherwise
      = do wcs' <- go_wc (ic_wanted impl)
           lift $ setImplicationStatus $ impl { ic_wanted = wcs' }    

solveImplicationUsingUnsatGiven :: (AnyKiEvVar AnyKiVar, AnyMonoKind) -> Implication -> TcS (Maybe Implication)
solveImplicationUsingUnsatGiven unsat_given@(given_ev, _) impl@(Implic { ic_wanted = wtd
                                                                       , ic_tclvl = tclvl
                                                                       , ic_binds = ev_binds_var
                                                                       , ic_need_inner = inner })
  | isKiCoEvBindsVar ev_binds_var
  = return $ Just impl
  | otherwise
  = do wcs <- nestImplicTcS ev_binds_var tclvl $ go_wc wtd
       setImplicationStatus $ impl { ic_wanted = wcs
                                   , ic_need_inner = inner `extendVarSet` given_ev }
  where
    go_wc :: WantedConstraints -> TcS WantedConstraints
    go_wc wc@(WC { wc_simple = wtds, wc_impl = impls }) = do
      mapBagM_ go_simple wtds
      impls <- mapMaybeBagM (solveImplicationUsingUnsatGiven unsat_given) impls
      return $ wc { wc_simple = emptyBag, wc_impl = impls }

    go_simple :: Ct -> TcS ()
    go_simple ct = case ctEvidence ct of
      CtWanted { ctev_pred = pki, ctev_dest = dst }
        -> do ev_type <- unsatisfiableKiEvType unsat_given pki
              panic "setWantedKiEvType dst True ev_type"
      _ -> return ()

unsatisfiableKiEvType :: (AnyKiEvVar AnyKiVar, AnyMonoKind) -> AnyMonoKind -> TcS AnyType
unsatisfiableKiEvType (unsat_ev, given_msg) wtd_ki = panic "unsatisfiableKiEvType"

{- *********************************************************************
*                                                                      *
                      Main Simplifier
*                                                                      *
********************************************************************* -}
 
solveWanteds :: WantedConstraints -> TcS WantedConstraints
solveWanteds wc
  | isEmptyWC wc
  = return wc
  | otherwise
  = do cur_lvl <- TcS.getTcLevel
       traceTcS "solveWanteds {"
         $ vcat [ text "Level =" <+> ppr cur_lvl
                , ppr wc ]

       dflags <- getDynFlags
       solved_wc <- simplify_loop 0 (solverIterations dflags) True wc

       traceTcS "solveWanteds }"
         $ vcat [ text "final wc =" <+> ppr solved_wc ]

       return solved_wc

simplify_loop :: Int -> IntWithInf -> Bool -> WantedConstraints -> TcS WantedConstraints
simplify_loop n limit definitely_redo_implications
              wc@(WC { wc_simple = simples, wc_impl = implics }) = do
  csTraceTcS $ text "simplify_loop iteration=" <> int n
               <+> (parens $ hsep [ text "definitely_redo ="
                                    <+> ppr definitely_redo_implications
                                    <> comma
                                  , int (lengthBag simples) <+> text "simples to solve" ])
  traceTcS "simplify_loop: wc =" (ppr wc)

  (unifs1, wc1) <- reportUnifications $ solveSimpleWanteds simples

  wc2 <- if not definitely_redo_implications
            && unifs1 == 0
            && isEmptyBag (wc_impl wc1)
         then return $ wc { wc_simple = wc_simple wc1 }
         else do implics2 <- solveNestedImplications
                             $ implics `unionBags` (wc_impl wc1)
                 return $ wc { wc_simple = wc_simple wc1
                             , wc_impl = implics2 }

  unif_happened <- resetUnificationFlag
  csTraceTcS $ text "unif_happened" <+> ppr unif_happened

  maybe_simplify_again (n+1) limit unif_happened wc2
  
maybe_simplify_again
  :: Int
  -> IntWithInf
  -> Bool
  -> WantedConstraints
  -> TcS WantedConstraints
maybe_simplify_again n limit unif_happened wc@(WC { wc_simple = simples })
  | n `intGtLimit` limit
  = do addErrTcS $ TcRnSimplifierTooManyIterations simples limit wc
       return wc
  | unif_happened
  = simplify_loop n limit True wc
  | otherwise
  = return wc

solveNestedImplications :: Bag Implication -> TcS (Bag Implication)
solveNestedImplications implics
  | isEmptyBag implics
  = return emptyBag
  | otherwise
  = do traceTcS "solveNestedImplications starting {" empty
       unsolved_implics <- mapBagM solveImplication implics
       traceTcS "solveNestedImplications end }"
         $ vcat [ text "unsolved_implics =" <+> ppr unsolved_implics ]

       return (catBagMaybes unsolved_implics)

solveImplication :: Implication -> TcS (Maybe Implication)
solveImplication imp@(Implic { ic_tclvl = tclvl
                             , ic_binds = ev_binds_var
                             , ic_given = given_ids
                             , ic_wanted = wanteds
                             , ic_info = info
                             , ic_status = status })
  | isSolvedStatus status
  = return $ Just imp
  | otherwise
  = do inerts <- getInertSet
       traceTcS "solveImplication {" (ppr imp $$ text "Inerts" <+> ppr inerts)

       (has_given_eqs, given_insols, residual_wanted)
         <- nestImplicTcS ev_binds_var tclvl $ 
            do let loc = mkGivenLoc tclvl info (ic_env imp)
                   givens = mkGivens loc given_ids
               solveSimpleGivens givens
               
               residual_wanted <- solveWanteds wanteds

               (has_eqs, given_insols) <- getHasGivenEqs tclvl

               return (has_eqs, given_insols, residual_wanted)

       traceTcS "solveImplication 2"
         (ppr given_insols $$ ppr residual_wanted)

       let final_wanted = residual_wanted `addInsols` given_insols

       res_implic <- setImplicationStatus (imp { ic_given_eqs = has_given_eqs
                                               , ic_wanted = final_wanted })

       evbinds <- TcS.getTcKiEvBindsMap ev_binds_var
       traceTcS "solveImplication end }"
         $ vcat [ text "has_given_eqs =" <+> ppr has_given_eqs
                , text "res_implic =" <+> ppr res_implic
                , text "implication evbinds =" <+> ppr (kiEvBindMapBinds evbinds) ]

       return res_implic                   

setImplicationStatus :: Implication -> TcS (Maybe Implication)
setImplicationStatus implic@(Implic { ic_status = status
                                    , ic_info = info
                                    , ic_wanted = wc
                                    , ic_given = givens })
  | assertPpr (not (isSolvedStatus status)) (ppr info)
    $ not (isSolvedWC pruned_wc)
  = do traceTcS "setImplicationStatus(not-all-solved) {" (ppr implic)
       let new_status | insolubleWC pruned_wc = IC_Insoluble
                      | otherwise = IC_Unsolved
           new_implic = implic { ic_status = new_status
                               , ic_wanted = pruned_wc }

       traceTcS "setImplicationStatus(not-all-solved) }" (ppr new_implic)

       return $ Just new_implic

  | otherwise
  = do traceTcS "setImplicationStatus(all-solved) {" (ppr implic)

       implic@(Implic { ic_need_inner = need_inner
                      , ic_need_outer = need_outer }) <- neededKiEvVars implic

       bad_telescope <- checkBadTelescope implic

       let warn_givens = findUnnecessaryGivens info need_inner givens

           discard_entire_implication
             = null warn_givens
               && not bad_telescope
               && isEmptyWC pruned_wc
               && isEmptyVarSet need_outer

           final_status
             | bad_telescope = IC_BadTelescope
             | otherwise = IC_Solved { ics_dead = warn_givens }

           final_implic = implic { ic_status = final_status
                                 , ic_wanted = pruned_wc }

       traceTcS "setImplicationStatus(all-solved) }"
         $ vcat [ text "discard:" <+> ppr discard_entire_implication
                , text "new_implic:" <+> ppr final_implic ]

       return $ if discard_entire_implication
                then Nothing
                else Just final_implic
  where
    WC { wc_simple = simples, wc_impl = implics } = wc

    pruned_implics = filterBag keep_me implics

    pruned_wc = WC { wc_simple = simples
                   , wc_impl = pruned_implics }

    keep_me ic
      | IC_Solved dead_givens <- ic_status ic
      , null dead_givens
      , isEmptyBag (wc_impl (ic_wanted ic))
      = False
      | otherwise
      = True

findUnnecessaryGivens :: SkolemInfoAnon -> MkVarSet (AnyKiEvVar AnyKiVar) -> [AnyKiEvVar AnyKiVar] -> [AnyKiEvVar AnyKiVar]
findUnnecessaryGivens info need_inner givens
  | not (warnRedundantGivens info)
  = []
  | not (null unused_givens)
  = unused_givens
  | otherwise
  = redundant_givens
  where
    unused_givens = filterOut is_used givens

    is_used given = given `elemVarSet` need_inner

    minimal_givens = mkMinimalBy kiEvVarPred givens
    is_minimal = (`elemVarSet` mkVarSet minimal_givens)

    redundant_givens = filterOut is_minimal givens

checkBadTelescope :: Implication -> TcS Bool
checkBadTelescope (Implic { ic_info = info, ic_skols = skols })
  | checkTelescopeSkol info
  = panic "checkBadTelescope"
  | otherwise
  = return False

warnRedundantGivens :: SkolemInfoAnon -> Bool
warnRedundantGivens (SigSkol ctxt _ _) = case ctxt of
  FunSigCtxt _ rrc -> reportRedundantConstraints rrc
  ExprSigCtxt rrc -> reportRedundantConstraints rrc
  _ -> False
warnRedundantGivens _ = False

neededKiEvVars :: Implication -> TcS Implication
neededKiEvVars implic@(Implic { ic_given = givens
                              , ic_binds = ev_binds_var
                              , ic_wanted = WC { wc_impl = implics }
                              , ic_need_inner = old_needs }) = do
  ev_binds <- TcS.getTcKiEvBindsMap ev_binds_var
  kcvs <- TcS.getTcKiEvKiCoVars ev_binds_var

  let seeds1 = foldr add_implic_seeds old_needs implics
      seeds2 = panic "nonDetStrictFoldKiEvBindMap add_wanted seeds1 ev_binds"
      seeds3 = seeds2 `unionVarSet` kcvs
      need_inner = findNeededKiEvVars ev_binds seeds3
      live_ev_binds = filterKiEvBindMap (needed_ev_bind need_inner) ev_binds
      need_outer = panic "varSetMinusKiEvBindMap need_inner live_ev_binds `delVarSetList` givens"

  TcS.setTcKiEvBindsMap ev_binds_var live_ev_binds

  traceTcS "neededKiEvVars"
    $ vcat [ text "old_needs:" <+> ppr old_needs
           , text "seeds3:" <+> ppr seeds3
           , text "kcvs:" <+> ppr kcvs
           , text "ev_binds:" <+> ppr ev_binds
           , text "live_ev_binds:" <+> ppr live_ev_binds ]

  return $ implic { ic_need_inner = panic "need_inner"
                  , ic_need_outer = panic "need_outer" }
  where
    add_implic_seeds (Implic { ic_need_outer = needs }) acc = needs `unionVarSet` acc

    needed_ev_bind needed (KiEvBind { keb_lhs = ev_var, keb_info = info })
      | KiEvBindGiven <- info = ev_var `elemVarSet` needed
      | otherwise = True

    --add_wanted :: KiEvBind -> VarSet -> VarSet
    add_wanted (KiEvBind { keb_info = info, keb_rhs = rhs }) needs
      | KiEvBindGiven <- info = needs
      | otherwise = kiEvVarsOfType rhs `unionVarSet` needs
