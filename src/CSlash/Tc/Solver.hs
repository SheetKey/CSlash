{-# LANGUAGE TupleSections #-}

module CSlash.Tc.Solver where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

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
import CSlash.Types.Var.Id
import CSlash.Utils.Outputable
import CSlash.Builtin.Utils
import CSlash.Builtin.Names
import CSlash.Tc.Errors
import CSlash.Tc.Errors.Types
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Solver.Solve ( solveSimpleWanteds, solveSimpleTyGivens
                              , solveSimpleKiGivens, solveSimpleKiWanteds )
-- import GHC.Tc.Solver.Dict    ( makeSuperClasses, solveCallStack )
-- import GHC.Tc.Solver.Rewrite ( rewriteType )
import CSlash.Tc.Utils.Unify    ( buildKvImplication )
import CSlash.Tc.Utils.TcMType as TcM
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

captureTopConstraints :: TcM a -> TcM (a, WantedTyConstraints)
captureTopConstraints thing_inside = do
  static_wc_var <- TcM.newTcRef emptyWC
  (mb_res, lie) <- TcM.updGblEnv (\env -> env { tcg_static_wc = static_wc_var })
                                 $ TcM.tryCaptureConstraints thing_inside
  stWC <- TcM.readTcRef static_wc_var
  case mb_res of
    Just res -> return (res, lie `andWC` stWC)
    Nothing -> do _ <- simplifyTop lie
                  failM

simplifyTop :: WantedTyConstraints -> TcM ()
simplifyTop wanteds = do 
  traceTc "simplifyTop {" $ text "wanted = " <+> ppr wanteds
  final_wc <- runTcS $ simplifyTopWanteds wanteds
  traceTc "End simplifyTop }" empty

  reportUnsolved final_wc

pushLevelAndSolveKindCoercions :: SkolemInfoAnon -> [TcKiVar] -> TcM a -> TcM a
pushLevelAndSolveKindCoercions skol_info_anon tcbs thing_inside = do
  (tclvl, wanted, res) <- pushLevelAndSolveKindCoercionsX
                          "pushLevelAndSolveKindCoercions" thing_inside
  report_unsolved_kicos skol_info_anon tcbs tclvl wanted
  return res

pushLevelAndSolveKindCoercionsX :: String -> TcM a -> TcM (TcLevel, WantedKiConstraints, a)
pushLevelAndSolveKindCoercionsX callsite thing_inside = do
  traceTc "pushLevelAndSolveKindCoercionsX {" (text "Called from" <+> text callsite)
  (tclvl, (wanted, res)) <- pushTcLevelM $ do
    (res, wanted) <- captureConstraints thing_inside
    wanted <- case onlyWantedKiConstraints_maybe wanted of
                Just w -> return w
                _ -> pprPanic "pushLevelAndSolveKindCoercionsX type constraints" (ppr wanted)
    wanted <- runTcSKindCoercions (simplifyTopKiWanteds wanted)
    return (wanted, res)
  traceTc "pushLevelAndSolveKindCoercionsX }" (vcat [ text "Residual:" <+> ppr wanted
                                                    , text "Level:" <+> ppr tclvl ])
  return (tclvl, wanted, res)

solveKindCoercions :: String -> TcM a -> TcM a
solveKindCoercions callsite thing_inside = do
  traceTc "solveKindCoercions {" (text "Called from" <+> text callsite)
  (res, wanted) <- captureConstraints thing_inside
  wanted <- onlyWantedKiConstraints wanted
  simplifyAndEmitFlatConstraints wanted
  traceTc "solveKindCoercions }" empty
  return res

simplifyAndEmitFlatConstraints :: WantedKiConstraints -> TcM ()
simplifyAndEmitFlatConstraints wanted = do
  wanted <- runTcSKindCoercions (solveKiWanteds wanted)
  wanted <- TcM.liftZonkM $ TcM.zonkWKC wanted

  traceTc "emitFlatConstraints {" (ppr wanted)
  case floatKindEqualities wanted of
    Nothing -> do traceTc "emitFlatConstraints } failing" (ppr wanted)
                  tclvl <- TcM.getTcLevel
                  implic <- buildKvImplication unkSkolAnon [] (pushTcLevel tclvl) wanted
                  emitKiImplication implic
                  failM
    Just simples -> do _ <- promoteKiVarSet (varsOfKiCts simples)
                       traceTc "emitFlatConstraints }"
                         $ vcat [ text "simples:" <+> ppr simples ]
                       emitKiSimples simples

floatKindEqualities :: WantedKiConstraints -> Maybe (Bag KiCt)
floatKindEqualities wc = float_wc emptyVarSet wc
  where
    float_wc :: KiVarSet Tc -> WantedKiConstraints -> Maybe (Bag KiCt)
    float_wc trapping_kvs (WKC { wkc_simple = simples, wkc_impl = implics })
      | all is_floatable simples
      = do inner_simples <- flatMapBagM (float_implic trapping_kvs) implics
           return $ simples `unionBags` inner_simples
      | otherwise
      = Nothing
      where
        is_floatable ct
          | insolubleCt ct = False
          | otherwise = varsOfKiCt ct `disjointVarSet` trapping_kvs

    float_implic :: KiVarSet Tc -> KiImplication -> Maybe (Bag KiCt)
    float_implic trapping_kvs (KiImplic { kic_wanted = wanted
                                        , kic_given_kicos = given_kicos
                                        , kic_skols = skols
                                        , kic_status = status })
      | isInsolubleStatus status
      = Nothing
      | otherwise
      = do simples <- float_wc (trapping_kvs `extendVarSetList` (TcKiVar <$> skols)) wanted
           when (not (isEmptyBag simples) && given_kicos == MaybeGivenKiCos) $ Nothing
           return simples

reportUnsolvedKiCos
  :: SkolemInfo
  -> [TcKiVar]
  -> TcLevel
  -> WantedKiConstraints
  -> TcM ()
reportUnsolvedKiCos skol_info skol_kvs tclvl wanted
  = report_unsolved_kicos (getSkolemInfo skol_info) skol_kvs tclvl wanted

report_unsolved_kicos
  :: SkolemInfoAnon -> [TcKiVar] -> TcLevel -> WantedKiConstraints -> TcM ()
report_unsolved_kicos skol_info_anon skol_vs tclvl wanted
  | isEmptyWC wanted
  = return ()
  | otherwise
  = checkNoErrs $ do
      implic <- buildKvImplication skol_info_anon skol_vs tclvl wanted
      reportAllUnsolved (mkKiImplicWC (unitBag implic))

simplifyTopWanteds :: WantedTyConstraints -> TcS WantedTyConstraints
simplifyTopWanteds wanteds = do
  wc_first_go <- nestTcS (solveWanteds wanteds)
  tryUnsatisfiableGivens wc_first_go

simplifyTopKiWanteds :: WantedKiConstraints -> TcS WantedKiConstraints
simplifyTopKiWanteds wanteds = do
  wc_first_go <- nestKiTcS (solveKiWanteds wanteds)
  useUnsatisfiableGivens wc_first_go

-- We never 'put True' since we don't have 'Unsatisfiable' class constraints.
-- Probably can remove these funcs.
tryUnsatisfiableGivens:: WantedTyConstraints -> TcS WantedTyConstraints
tryUnsatisfiableGivens wc = do
  (final_wc, did_work) <- (`runStateT` False) $ go_wc wc
  if did_work
    then nestTcS (solveWanteds final_wc)
    else return final_wc
  where
    go_wc (WTC { wtc_simple = wtds, wtc_impl = impls, wtc_wkc = wkc })  = do
      final_wkc <- lift $ useUnsatisfiableGivens wkc
      impls' <- mapMaybeBagM go_impl impls
      return $ WTC { wtc_simple = wtds, wtc_impl = impls', wtc_wkc = final_wkc }

    go_impl impl
      | isSolvedStatus (tic_status impl)
      = return $ Just impl
      | otherwise
      = do wcs' <- go_wc (tic_wanted impl)
           lift $ setTyImplicationStatus $ impl { tic_wanted = wcs' }

useUnsatisfiableGivens :: WantedKiConstraints -> TcS WantedKiConstraints
useUnsatisfiableGivens wc = do
  (final_wc, did_work) <- (`runStateT` False) $ go_wc wc
  if did_work
    then nestTcS (solveKiWanteds final_wc)
    else return final_wc
  where
    go_wc (WKC { wkc_simple = wtds, wkc_impl = impls }) = do
      impls' <- mapMaybeBagM go_impl impls
      return $ WKC { wkc_simple = wtds, wkc_impl = impls' }

    go_impl impl
      | isSolvedStatus (kic_status impl)
      = return $ Just impl
      | otherwise
      = do wcs' <- go_wc (kic_wanted impl)
           lift $ setKiImplicationStatus $ impl { kic_wanted = wcs' }    

-- solveKiImplicationUsingUnsatGiven
--   :: (KiCoVar AnyKiVar, AnyMonoKind)
--   -> KiImplication
--   -> TcS (Maybe KiImplication)
-- solveKiImplicationUsingUnsatGiven unsat_given@(given_ev, _)
--   impl@(KiImplic { kic_wanted = wtd
--                  , kic_tclvl = tclvl
--                  , kic_binds = ev_binds_var
--                  , kic_need_inner = inner })
--   = do wcs <- nestKiImplicTcS ev_binds_var tclvl $ go_wc wtd
--        setKiImplicationStatus $ impl { kic_wanted = wcs
--                                    , kic_need_inner = inner `extendVarSet` given_ev }
--   where
--     go_wc :: WantedKiConstraints -> TcS WantedKiConstraints
--     go_wc wc@(WKC { wkc_simple = wtds, wkc_impl = impls }) = do
--       mapBagM_ go_simple wtds
--       impls <- mapMaybeBagM (solveKiImplicationUsingUnsatGiven unsat_given) impls
--       return $ wc { wkc_simple = emptyBag, wkc_impl = impls }

--     go_simple :: KiCt -> TcS ()
--     go_simple ct = case ctKiEvidence ct of
--       CtKiWanted { ctkev_pred = pki, ctkev_dest = dst }
--         -> do ev_type <- unsatisfiableKiEvType unsat_given pki
--               panic "setWantedKiEvType dst True ev_type"
--       _ -> return ()

-- unsatisfiableKiEvType :: (KiCoVar AnyKiVar, AnyMonoKind) -> AnyMonoKind -> TcS AnyType
-- unsatisfiableKiEvType (unsat_ev, given_msg) wtd_ki = panic "unsatisfiableKiEvType"

{- *********************************************************************
*                                                                      *
                      Inference
*                                                                      *
********************************************************************* -}

data InferMode = ApplyMR

instance Outputable InferMode where
  ppr ApplyMR = text "ApplyMR"

simplifyInfer
  :: TcLevel
  -> InferMode
  -> [(Name, TauType Tc)]
  -> WantedTyConstraints
  -> TcM ([TcKiVar], [TcTyVar], Bool)
simplifyInfer rhs_tclvl infer_mode name_taus wanteds
  | isEmptyWC wanteds
  = do dep_vars <- candidateQTyKiVarsOfTypes (map snd name_taus)

       skol_info <- mkSkolemInfo (InferSkol name_taus)
       qtkvs@(qkvs, qtvs) <- quantifyTyKiVars skol_info dep_vars
       traceTc "simplifyInfer: empty WC" (ppr name_taus $$ ppr qtkvs)
       return (qkvs, qtvs, False)

  | otherwise
  = do traceTc "simplifyInfer {"
         $ vcat [ text "binds =" <+> ppr name_taus
                , text "rhs_tclvl =" <+> ppr rhs_tclvl
                , text "(unzonked) wanted =" <+> ppr wanteds ]
       undefined

{- *********************************************************************
*                                                                      *
                      Main Simplifier
*                                                                      *
********************************************************************* -}

solveWanteds :: WantedTyConstraints -> TcS WantedTyConstraints
solveWanteds wc@(WTC { wtc_wkc = wkc })
  | isEmptyWC wc
  = return wc
  | otherwise
  = do cur_lvl <- TcS.getTcLevel
       traceTcS "solveWanteds {"
         $ vcat [ text "Level =" <+> ppr cur_lvl
                , ppr wc ]

       dflags <- getDynFlags
       solved_wc <- simplify_loop 0 (solverIterations dflags) True wc

       traceTcS "solvedWanteds }"
         $ vcat [ text "final wc =" <+> ppr solved_wc ]

       return solved_wc
 
solveKiWanteds :: WantedKiConstraints -> TcS WantedKiConstraints
solveKiWanteds wc
  | isEmptyWC wc
  = return wc
  | otherwise
  = do cur_lvl <- TcS.getTcLevel
       traceTcS "solveKiWanteds {"
         $ vcat [ text "Level =" <+> ppr cur_lvl
                , ppr wc ]

       dflags <- getDynFlags
       solved_wc <- simplify_ki_loop 0 (solverIterations dflags) True wc

       traceTcS "solveKiWanteds }"
         $ vcat [ text "final wc =" <+> ppr solved_wc ]

       return solved_wc

simplify_loop :: Int -> IntWithInf -> Bool -> WantedTyConstraints -> TcS WantedTyConstraints
simplify_loop n limit definitely_redo_implications
  wtc@(WTC { wtc_simple = ty_simples
           , wtc_impl = ty_implics
           , wtc_wkc = wkc@(WKC { wkc_simple = ki_simples
                                , wkc_impl = ki_implics }) })
  = do csTraceTcS
         $ text "simplify_loop iteration=" <> int n
         <+> (parens $ hsep [ text "definitely_redo =" <+> ppr definitely_redo_implications
                              <> comma
                            , int (lengthBag ty_simples) <+> text "type simples to solve"
                              <> comma
                            , int (lengthBag ki_simples) <+> text "kind simples to solve" ])

       traceTcS "simplify_loop: wc =" (ppr wtc)

       (unifs1, wtc1) <- reportUnifications $ solveSimpleWanteds ty_simples ki_simples

       wtc2 <- if not definitely_redo_implications
                  && unifs1 == 0
                  && isEmptyBag (wtc_impl wtc1)
                  && isEmptyBag (wkc_impl (wtc_wkc wtc1))
              then return (wtc { wtc_simple = wtc_simple wtc1
                               , wtc_wkc = wkc { wkc_simple = wkc_simple (wtc_wkc wtc1) } })
              else do (ty_implics2, ki_implics2) <- solveNestedImplications
                        (ty_implics `unionBags` (wtc_impl wtc1))
                        (ki_implics `unionBags` (wkc_impl (wtc_wkc wtc1)))
                      return $ wtc { wtc_simple = wtc_simple wtc1
                                   , wtc_impl = ty_implics2
                                   , wtc_wkc = wkc { wkc_simple = wkc_simple (wtc_wkc wtc1)
                                                   , wkc_impl = ki_implics2 } }

       unif_happened <- resetUnificationFlag
       csTraceTcS $ text "unif_happened" <+> ppr unif_happened

       maybe_simplify_again (n+1) limit unif_happened wtc2

simplify_ki_loop :: Int -> IntWithInf -> Bool -> WantedKiConstraints -> TcS WantedKiConstraints
simplify_ki_loop n limit definitely_redo_implications
              wc@(WKC { wkc_simple = simples, wkc_impl = implics }) = do
  csTraceTcS $ text "simplify_ki_loop iteration=" <> int n
               <+> (parens $ hsep [ text "definitely_redo ="
                                    <+> ppr definitely_redo_implications
                                    <> comma
                                  , int (lengthBag simples) <+> text "simples to solve" ])
  traceTcS "simplify_ki_loop: wc =" (ppr wc)

  (unifs1, wc1) <- reportUnifications $ solveSimpleKiWanteds simples

  wc2 <- if not definitely_redo_implications
            && unifs1 == 0
            && isEmptyBag (wkc_impl wc1)
         then return $ wc { wkc_simple = wkc_simple wc1 }
         else do implics2 <- solveNestedKiImplications
                             $ implics `unionBags` (wkc_impl wc1)
                 return $ wc { wkc_simple = wkc_simple wc1
                             , wkc_impl = implics2 }

  unif_happened <- resetUnificationFlag
  csTraceTcS $ text "unif_happened" <+> ppr unif_happened

  maybe_simplify_ki_again (n+1) limit unif_happened wc2

maybe_simplify_again
  :: Int
  -> IntWithInf
  -> Bool
  -> WantedTyConstraints
  -> TcS WantedTyConstraints
maybe_simplify_again n limit unif_happened wtc@(WTC { wtc_simple = ty_simples
                                                    , wtc_wkc = WKC { wkc_simple = ki_simples }})
  | n `intGtLimit` limit
  = do addErrTcS $ panic "TcRnSimplifierTooManyIterations ty_simples ki_simples limit wc"
       return wtc
  | unif_happened
  = simplify_loop n limit True wtc
  | otherwise
  = return wtc
  
maybe_simplify_ki_again
  :: Int
  -> IntWithInf
  -> Bool
  -> WantedKiConstraints
  -> TcS WantedKiConstraints
maybe_simplify_ki_again n limit unif_happened wc@(WKC { wkc_simple = simples })
  | n `intGtLimit` limit
  = do addErrTcS $ TcRnSimplifierTooManyIterations simples limit wc
       return wc
  | unif_happened
  = simplify_ki_loop n limit True wc
  | otherwise
  = return wc

solveNestedImplications
  :: Bag TyImplication -> Bag KiImplication
  -> TcS (Bag TyImplication, Bag KiImplication)
solveNestedImplications ty_implics ki_implics
  | isEmptyBag ty_implics
  = if isEmptyBag ki_implics
    then return (emptyBag, emptyBag)
    else do ki_implics' <- solveNestedKiImplications ki_implics
            return (emptyBag, ki_implics')
  | otherwise
  = do traceTcS "solveNestedImplications starting {" empty
       unsolved_ki_implics <- solveNestedKiImplications ki_implics
       unsolved_ty_implics <- mapBagM solveTyImplication ty_implics
       traceTcS "solveNestedImplications end }"
         $ vcat [ text "unsolved_ty_implics =" <+> ppr unsolved_ty_implics ]

       return (catBagMaybes unsolved_ty_implics, unsolved_ki_implics)

solveNestedKiImplications :: Bag KiImplication -> TcS (Bag KiImplication)
solveNestedKiImplications implics
  | isEmptyBag implics
  = return emptyBag
  | otherwise
  = do traceTcS "solveNestedKiImplications starting {" empty
       unsolved_implics <- mapBagM solveKiImplication implics
       traceTcS "solveNestedKiImplications end }"
         $ vcat [ text "unsolved_implics =" <+> ppr unsolved_implics ]

       return (catBagMaybes unsolved_implics)

solveKiImplication :: KiImplication -> TcS (Maybe KiImplication)
solveKiImplication imp@(KiImplic { kic_tclvl = tclvl
                               , kic_binds = ev_binds_var
                               , kic_given = given_ids
                               , kic_wanted = wanteds
                               , kic_info = info
                               , kic_status = status })
  | isSolvedStatus status
  = return $ Just imp
  | otherwise
  = do inerts <- getInertKiSet
       traceTcS "solveKiImplication {" (ppr imp $$ text "Inerts" <+> ppr inerts)

       (has_given_kicos, given_insols, residual_wanted)
         <- nestKiImplicTcS ev_binds_var tclvl $ 
            do let loc = mkGivenLoc tclvl info (kic_env imp)
                   givens = mkKiGivens loc given_ids
               solveSimpleKiGivens givens
               
               residual_wanted <- solveKiWanteds wanteds

               (has_kicos, given_insols) <- getHasGivenKiCos tclvl

               return (has_kicos, given_insols, residual_wanted)

       traceTcS "solveKiImplication 2"
         (ppr given_insols $$ ppr residual_wanted)

       let final_wanted = residual_wanted `addKiInsols` given_insols

       res_implic <- setKiImplicationStatus (imp { kic_given_kicos = has_given_kicos
                                               , kic_wanted = final_wanted })

       kcvs <- TcS.getTcKiCoVars ev_binds_var
       traceTcS "solveKiImplication end }"
         $ vcat [ text "has_given_kicos =" <+> ppr has_given_kicos
                , text "res_implic =" <+> ppr res_implic ]

       return res_implic                   

solveTyImplication :: TyImplication -> TcS (Maybe TyImplication)
solveTyImplication imp@(TyImplic { tic_tclvl = tclvl
                                 , tic_binds = ev_binds_var
                                 , tic_given = given_ids
                                 , tic_wanted = wanteds
                                 , tic_info = info
                                 , tic_status = status })
  | isSolvedStatus status
  = return $ Just imp
  | otherwise
  = do inerts <- getInertTySet
       traceTcS "solveTyImplication {" (ppr imp $$ text "Inerts" <+> ppr inerts)

       (has_given_eqs, given_insols, residual_wanted)
         <- nestTyImplicTcS ev_binds_var tclvl $
            do let loc = mkGivenLoc tclvl info (tic_env imp)
                   givens = mkTyGivens loc given_ids
               solveSimpleTyGivens givens
               residual_wanted <- solveWanteds wanteds
               (has_eqs, given_insols) <- getHasGivenTyEqs tclvl
               return (has_eqs, given_insols, residual_wanted)

       traceTcS "solveTyImplication 2"
         (ppr given_insols $$ ppr residual_wanted)
       let final_wanted = residual_wanted `addTyInsols` given_insols

       res_implic <- setTyImplicationStatus (imp { tic_given_eqs = has_given_eqs
                                                 , tic_wanted = final_wanted })

       tcvs <- TcS.getTcTyCoVars ev_binds_var
       traceTcS "solveTyImplication end }"
         $ vcat [ text "has_given_eqs =" <+> ppr has_given_eqs
                , text "res_implic =" <+> ppr res_implic
                , text "implication tcvs =" <+> ppr tcvs ]

       return res_implic

setKiImplicationStatus :: KiImplication -> TcS (Maybe KiImplication)
setKiImplicationStatus implic@(KiImplic { kic_status = status
                                      , kic_info = info
                                      , kic_wanted = wc
                                      , kic_given = givens })
  | assertPpr (not (isSolvedStatus status)) (ppr info)
    $ not (isSolvedWC pruned_wc)
  = do traceTcS "setKiImplicationStatus(not-all-solved) {" (ppr implic)
       implic <- neededKiCoVars implic
       let new_status | insolubleWC pruned_wc = IC_Insoluble
                      | otherwise = IC_Unsolved
           new_implic = implic { kic_status = new_status
                               , kic_wanted = pruned_wc }

       traceTcS "setKiImplicationStatus(not-all-solved) }" (ppr new_implic)

       return $ Just new_implic

  | otherwise
  = do traceTcS "setKiImplicationStatus(all-solved) {" (ppr implic)

       implic@(KiImplic { kic_need_inner = need_inner
                        , kic_need_outer = need_outer }) <- neededKiCoVars implic

       bad_telescope <- checkBadKiTelescope implic

       let warn_givens = findUnnecessaryKiGivens info need_inner givens

           discard_entire_implication
             = null warn_givens
               && not bad_telescope
               && isEmptyWC pruned_wc
               && isEmptyVarSet need_outer

           final_status
             | bad_telescope = IC_BadTelescope
             | otherwise = IC_Solved { ics_dead = warn_givens }

           final_implic = implic { kic_status = final_status
                                 , kic_wanted = pruned_wc }

       traceTcS "setKiImplicationStatus(all-solved) }"
         $ vcat [ text "discard:" <+> ppr discard_entire_implication
                , text "new_implic:" <+> ppr final_implic ]

       return $ if discard_entire_implication
                then Nothing
                else Just final_implic
  where
    WKC { wkc_simple = simples, wkc_impl = implics } = wc

    pruned_implics = filterBag keep_me implics

    pruned_wc = WKC { wkc_simple = simples
                   , wkc_impl = pruned_implics }

    keep_me ic
      | IC_Solved dead_givens <- kic_status ic
      , null dead_givens
      , isEmptyBag (wkc_impl (kic_wanted ic))
      = False
      | otherwise
      = True

setTyImplicationStatus :: TyImplication -> TcS (Maybe TyImplication)
setTyImplicationStatus implic@(TyImplic { tic_status = old_status
                                        , tic_info = info
                                        , tic_wanted = wc
                                        , tic_given = givens })
  | assertPpr (not (isSolvedStatus old_status)) (ppr info)
    $ not (isSolvedWC pruned_wc)
  = do traceTcS "setTyImplicationStatus(not-all-solved) {" (ppr implic)
       implic <- neededTyCoVars implic

       let new_status | insolubleWC pruned_wc = IC_Insoluble
                      | otherwise = IC_Unsolved
           new_implic = implic { tic_status = new_status
                               , tic_wanted = pruned_wc }

       traceTcS "setTyImplicationStatus(not-all-solved) }" (ppr new_implic)

       return $ Just new_implic

  | otherwise
  = do traceTcS "setTyImplicationStatus(all-solved) {" (ppr implic)

       implic@(TyImplic { tic_need_inner = need_inner
                        , tic_need_outer = need_outer }) <- neededTyCoVars implic

       bad_telescope <- checkBadTyTelescope implic

       let warn_givens = findUnnecessaryTyGivens info need_inner givens

           discard_entire_implication
             = null warn_givens
               && not bad_telescope
               && isEmptyWC pruned_wc
               && isEmptyVarSet need_outer

           final_status
             | bad_telescope = IC_BadTelescope
             | otherwise = IC_Solved { ics_dead = warn_givens }
           final_implic = implic { tic_status = final_status
                                 , tic_wanted = pruned_wc }

       traceTcS "setTyImplicationStatus(all-solved) }"
         $ vcat [ text "discard:" <+> ppr discard_entire_implication
                , text "new_implic:" <+> ppr final_implic ]

       return $ if discard_entire_implication
                then Nothing
                else Just final_implic

  where
    WTC { wtc_simple = simples
        , wtc_impl = implics
        , wtc_wkc = wkc } = wc

    WKC { wkc_simple = ki_simples
        , wkc_impl = ki_implics } = wkc

    pruned_ki_implics = filterBag keep_me_ki ki_implics
    pruned_implics = filterBag keep_me implics
    pruned_wc = WTC { wtc_simple = simples
                    , wtc_impl = pruned_implics
                    , wtc_wkc = WKC { wkc_simple = ki_simples
                                    , wkc_impl = pruned_ki_implics } }

    keep_me ic
      | IC_Solved { ics_dead = dead_givens } <- tic_status ic
      , null dead_givens
      , isEmptyBag (wtc_impl (tic_wanted ic))
      = False
      | otherwise
      = True

    keep_me_ki ic
      | IC_Solved dead_givens <- kic_status ic
      , null dead_givens
      , isEmptyBag (wkc_impl (kic_wanted ic))
      = False
      | otherwise
      = True

findUnnecessaryKiGivens
  :: SkolemInfoAnon
  -> KiCoVarSet Tc
  -> [KiCoVar Tc]
  -> [KiCoVar Tc]
findUnnecessaryKiGivens info need_inner givens
  | not (warnRedundantGivens info)
  = []
  | not (null unused_givens)
  = unused_givens
  | otherwise
  = redundant_givens
  where
    unused_givens = filterOut is_used givens

    is_used :: KiCoVar Tc -> Bool
    is_used given = given `elemVarSet` need_inner

    minimal_givens = mkMinimalBy_Ki kiCoVarPred givens
    is_minimal = (`elemVarSet` mkVarSet minimal_givens)

    redundant_givens = filterOut is_minimal givens

findUnnecessaryTyGivens
  :: SkolemInfoAnon
  -> TyCoVarSet Tc
  -> [TyCoVar Tc]
  -> [TyCoVar Tc]
findUnnecessaryTyGivens info need_inner givens
  | not (warnRedundantGivens info)
  = []
  | not (null unused_givens)
  = unused_givens
  | otherwise
  = redundant_givens
  where
    unused_givens = filterOut is_used givens

    is_used :: TyCoVar Tc -> Bool
    is_used given = given `elemVarSet` need_inner

    minimal_givens = mkMinimalBy_Ty tyCoVarPred givens
    is_minimal = (`elemVarSet` mkVarSet minimal_givens)

    redundant_givens = filterOut is_minimal givens      

checkBadKiTelescope :: KiImplication -> TcS Bool
checkBadKiTelescope (KiImplic { kic_info = info, kic_skols = skols })
  = return False

checkBadTyTelescope :: TyImplication -> TcS Bool
checkBadTyTelescope _ = return False

warnRedundantGivens :: SkolemInfoAnon -> Bool
warnRedundantGivens (SigSkol ctxt _ _) = case ctxt of
  FunSigCtxt _ rrc -> reportRedundantConstraints rrc
  ExprSigCtxt rrc -> reportRedundantConstraints rrc
  _ -> False
warnRedundantGivens _ = False

-- This might need to look into WKC.
-- Would require tic_need_inner/outer to include KiCoVars
neededTyCoVars :: TyImplication -> TcS TyImplication
neededTyCoVars implic@(TyImplic { tic_given = givens
                                , tic_binds = tyco_binds_var
                                , tic_wanted = WTC { wtc_impl = implics }
                                , tic_need_inner = old_needs })
  = do tcvs <- TcS.getTcTyCoVars tyco_binds_var

       let seeds1 = foldr add_implic_seeds old_needs implics
           need_inner = seeds1 `unionVarSet` tcvs
           need_outer = need_inner `delVarSetList` givens

       traceTcS "neededTyCoVars"
         $ vcat [ text "old_needs:" <+> ppr old_needs
                , text "seeds1:" <+> ppr seeds1
                , text "tcvs:" <+> ppr tcvs
                , text "need_inner:" <+> ppr need_inner
                , text "need_outer:" <+> ppr need_outer ]

       return $ implic { tic_need_inner = need_inner
                       , tic_need_outer = need_outer }
  where
    add_implic_seeds (TyImplic { tic_need_outer = needs }) acc = needs `unionVarSet` acc

neededKiCoVars :: KiImplication -> TcS KiImplication
neededKiCoVars implic@(KiImplic { kic_given = givens
                                , kic_binds = co_binds_var
                                , kic_wanted = WKC { wkc_impl = implics }
                                , kic_need_inner = old_needs }) = do 
  kcvs <- TcS.getTcKiCoVars co_binds_var

  let seeds1 = foldr add_implic_seeds old_needs implics
      need_inner = seeds1 `unionVarSet` kcvs
      need_outer = need_inner `delVarSetList` givens

  traceTcS "neededKiCoVars"
    $ vcat [ text "old_needs:" <+> ppr old_needs
           , text "seeds1:" <+> ppr seeds1
           , text "kcvs:" <+> ppr kcvs
           , text "need_inner:" <+> ppr need_inner
           , text "need_outer:" <+> ppr need_outer ]

  return $ implic { kic_need_inner = need_inner
                  , kic_need_outer = need_outer }
  where
    add_implic_seeds (KiImplic { kic_need_outer = needs }) acc = needs `unionVarSet` acc
