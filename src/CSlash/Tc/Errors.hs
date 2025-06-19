{-# LANGUAGE MultiWayIf #-}

module CSlash.Tc.Errors where

import Prelude hiding ((<>))

import CSlash.Driver.Env (cs_units)
import CSlash.Driver.DynFlags
import CSlash.Driver.Ppr
import CSlash.Driver.Config.Diagnostic

import CSlash.Rename.Unbound

import CSlash.Tc.Types
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Errors.Types
import CSlash.Tc.Errors.Ppr
import CSlash.Tc.Types.Constraint
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Zonk.Type
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Zonk.TcType
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.Evidence
-- import GHC.Tc.Types.EvTerm
-- import GHC.Tc.Instance.Family
import CSlash.Tc.Utils.Instantiate
import {-# SOURCE #-} CSlash.Tc.Errors.Hole ( {-findValidHoleFits,-}
  getHoleFitDispConfig{-, pprHoleFit-} )

import CSlash.Types.Name hiding (varName)
import CSlash.Types.Name.Reader
import CSlash.Types.Id
import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Types.Name.Env
import CSlash.Types.SrcLoc
import CSlash.Types.Basic
import CSlash.Types.Error
import qualified CSlash.Types.Unique.Map as UM

import CSlash.Unit.Module

import CSlash.Core.Predicate
import CSlash.Core.Type
import CSlash.Core.Type.FVs
import CSlash.Core.Type.Tidy
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs
import CSlash.Core.Kind.Compare
-- import GHC.Core.Coercion
import CSlash.Core.Type.Ppr ( pprTyVars )
-- import GHC.Core.InstEnv
import CSlash.Core.TyCon
import CSlash.Core.DataCon

import CSlash.Utils.Error (diagReasonSeverity,  pprLocMsgEnvelope )
import CSlash.Utils.Misc
import CSlash.Utils.Outputable as O
import CSlash.Utils.Panic
import CSlash.Utils.FV ( unionFV )

import CSlash.Data.Bag
import CSlash.Data.List.SetOps ( equivClasses, nubOrdBy )
import CSlash.Data.Maybe
import qualified CSlash.Data.Strict as Strict

import Control.Monad      ( unless, when, foldM, forM_ )
import Data.Foldable      ( toList )
import Data.Function      ( on )
import Data.List          ( partition, sort, sortBy )
import Data.List.NonEmpty ( NonEmpty(..), nonEmpty )
import qualified Data.List.NonEmpty as NE
import Data.Ord         ( comparing )
import qualified Data.Semigroup as S

{- *********************************************************************
*                                                                      *
         Errors and contexts
*                                                                      *
********************************************************************* -}

reportUnsolved :: WantedConstraints -> TcM (Bag KiEvBind)
reportUnsolved wanted = do
  binds_var <- newTcKiEvBinds
  defer_errors <- goptM Opt_DeferTypeErrors
  let type_errors | not defer_errors = ErrorWithoutFlag
                  | otherwise = panic "reportUnsolved DeferTypeErrors"

  defer_holes <- goptM Opt_DeferTypedHoles
  let expr_holes | not defer_holes = ErrorWithoutFlag
                 | otherwise = panic "reportUnsolved DeferTypedHoles"

  defer_out_of_scope <- goptM Opt_DeferOutOfScopeVariables
  let out_of_scope_holes | not defer_out_of_scope = ErrorWithoutFlag
                         | otherwise = panic "reportUnsolved DeferOutOfScopeVariables"

  report_unsolved type_errors expr_holes out_of_scope_holes binds_var wanted

  ev_binds <- getTcKiEvBindsMap binds_var
  return $ kiEvBindMapBinds ev_binds

reportAllUnsolved :: WantedConstraints -> TcM ()
reportAllUnsolved wanted = do
  ev_binds <- newNoTcKiEvBinds
  report_unsolved ErrorWithoutFlag ErrorWithoutFlag ErrorWithoutFlag ev_binds wanted

report_unsolved
  :: DiagnosticReason
  -> DiagnosticReason
  -> DiagnosticReason
  -> KiEvBindsVar
  -> WantedConstraints
  -> TcM ()
report_unsolved type_errors expr_holes out_of_scope_holes binds_var wanted
  | isEmptyWC wanted
  = return ()
  | otherwise
  = do traceTc "reportUnsolved {" 
         $ vcat [ text "type errors:" <+> ppr type_errors
                , text "expr holes:" <+> ppr expr_holes
                , text "scope holes:" <+> ppr out_of_scope_holes ]
       traceTc "reportUnsolved (before zonking and tidying)" (ppr wanted)

       wanted <- liftZonkM $ zonkWC wanted
       
       let free_kvs = varsOfWCList wanted
           tidy_env = panic "tidyFreeKiVars emptyTidyEnv free_kvs"

       traceTc "reportUnsolved (after zonking):"
         $ vcat [ text "Free kivars:" <+> ppr free_kvs
                , text "Tidy env:" <+> panic "ppr tidy_env"
                , text "Wanted:" <+> ppr wanted ]

       warn_redundant <- woptM Opt_WarnRedundantConstraints
       let err_ctxt = CEC { cec_encl = []
                          , cec_tidy = tidy_env
                          , cec_defer_type_errors = type_errors
                          , cec_expr_holes = expr_holes
                          , cec_out_of_scope_holes = out_of_scope_holes
                          , cec_suppress = insolubleWC wanted
                          , cec_warn_redundant = warn_redundant
                          , cec_binds = binds_var }
       tc_lvl <- getTcLevel
       reportWanteds err_ctxt tc_lvl wanted
       traceTc "reportUnsolved }" empty

--------------------------------------------
--      Internal functions
--------------------------------------------

important :: SolverReportErrCtxt -> TcSolverReportMsg -> SolverReport
important ctxt doc = SolverReport { sr_important_msg = SolverReportWithCtxt ctxt doc
                                  , sr_supplementary = [] }

add_relevant_bindings :: RelevantBindings -> SolverReport -> SolverReport
add_relevant_bindings binds report@(SolverReport { sr_supplementary = supp })
  = report { sr_supplementary = SupplementaryBindings binds : supp }

deferringAnyBindings :: SolverReportErrCtxt -> Bool
deferringAnyBindings (CEC { cec_defer_type_errors = ErrorWithoutFlag
                          , cec_expr_holes = ErrorWithoutFlag
                          , cec_out_of_scope_holes = ErrorWithoutFlag }) = False
deferringAnyBindings _ = True

maybeSwitchOffDefer :: KiEvBindsVar -> SolverReportErrCtxt -> SolverReportErrCtxt
maybeSwitchOffDefer evb ctxt
  | KiCoEvBindsVar {} <- evb
  = ctxt { cec_defer_type_errors = ErrorWithoutFlag
         , cec_expr_holes = ErrorWithoutFlag
         , cec_out_of_scope_holes = ErrorWithoutFlag }
  | otherwise
  = ctxt

reportImplic :: SolverReportErrCtxt -> Implication -> TcM ()
reportImplic ctxt implic@(Implic { ic_skols = tvs
                                 , ic_given = given
                                 , ic_wanted = wanted
                                 , ic_binds = evb
                                 , ic_status = status
                                 , ic_info = info
                                 , ic_env = ct_loc_env
                                 , ic_tclvl = tc_lvl }) = do
  traceTc "reportImplic"
    $ vcat [ text "tidy env:" <+> ppr (cec_tidy ctxt)
           , text "skols:" <+> ppr tvs
           , text "tidy skols:" <+> panic "ppr tvs'" ]

  when bad_telescope $ panic "reportBadTelescope ctxt ct_loc_ev info tvs"

  reportWanteds ctxt' tc_lvl wanted

  panic "warnRedundantConstraints ctxt' ct_loc_env info' dead_givens"
  where
    insoluble = isInsolubleStatus status
    (env1, tvs') = panic "tidyKiVarBndrs (cec_tidy ctxt) $ tvs"

    info' = panic "tidySkolemInfoAnon env1 info"
    implic' = implic { ic_skols = tvs'
                     , ic_given = panic "map (tidyKiEvVar env1) given"
                     , ic_info = info' }

    ctxt1 = maybeSwitchOffDefer evb ctxt
    ctxt' = ctxt1 { cec_tidy = panic "env1"
                  , cec_encl = implic' : cec_encl ctxt
                  , cec_suppress = insoluble || cec_suppress ctxt
                  , cec_binds = evb  }

    dead_givens = case status of
                    IC_Solved dead -> dead
                    _ -> []

    bad_telescope = case status of
      IC_BadTelescope -> True
      _ -> False

warnRedundantConstraints
  :: SolverReportErrCtxt
  -> CtLocEnv
  -> SkolemInfoAnon
  -> [TcKiEvVar TcKiVar]
  -> TcM ()
warnRedundantConstraints ctxt env info redundant_evs
  | not (cec_warn_redundant ctxt)
  = return ()
  | null redundant_evs
  = return ()
  | SigSkol user_ctxt _ _ <- info
  = panic "report_redundant_msg True (set"
  | otherwise
  = panic "report_redundant"

mkErrorItem :: Ct -> TcM (Maybe ErrorItem)
mkErrorItem ct = do
  let loc = ctLoc ct
      flav = ctFlavor ct
  (suppress, m_evdest) <- case ctEvidence ct of
    CtGiven {} -> return (False, Nothing)
    CtWanted { ctev_rewriters = rewriters, ctev_dest = dest } -> do
      rewriters' <- zonkRewriterSet rewriters
      return (not (isEmptyRewriterSet rewriters'), Just dest)
  let m_reason = case ct of
                   CIrredCan (IrredCt {ir_reason = reason}) -> Just reason
                   _ -> Nothing
  return $ Just $ EI { ei_pred = ctPred ct
                     , ei_evdest = m_evdest
                     , ei_flavor = flav
                     , ei_loc = loc
                     , ei_m_reason = m_reason
                     , ei_suppress = suppress }

unsuppressErrorItem :: ErrorItem -> ErrorItem
unsuppressErrorItem ei = ei { ei_suppress = False }

reportWanteds :: SolverReportErrCtxt -> TcLevel -> WantedConstraints -> TcM ()
reportWanteds ctxt tc_lvl wc@(WC { wc_simple = simples, wc_impl = implics })
  | isEmptyWC wc = traceTc "reportWanteds empty WC" empty
  | otherwise
  = do tidy_items1 <- mapMaybeM mkErrorItem tidy_cts
       traceTc "reportWanteds 1"
         $ vcat [ text "Simples =" <+> ppr simples
                , text "Suppress =" <+> ppr (cec_suppress ctxt)
                , text "tidy_cts =" <+> ppr tidy_cts
                , text "tidy_items1 =" <+> ppr tidy_items1 ]

       errs_already <- ifErrsM (return True) (return False)
       let tidy_items
             | not errs_already
             , all ei_suppress tidy_items1
             = map unsuppressErrorItem tidy_items1
             | otherwise
             = tidy_items1

           (suppressed_items, items0) = partition suppress tidy_items

           no_out_of_scope = True
           ctxt_for_insols = ctxt { cec_suppress = not no_out_of_scope }

       traceTc "reportWanteds suppressed:" (ppr suppressed_items)
       (ctxt1, items1) <- tryReporters ctxt_for_insols report1 items0

       let ctxt2 = ctxt1 { cec_suppress = cec_suppress ctxt || cec_suppress ctxt1 }
       (ctxt3, leftovers) <- tryReporters ctxt2 report2 items1
       massertPpr (null leftovers)
         (text "The following unsolved Wanted constraints \
               \have not been reported to the user:"
           $$ ppr leftovers)

       mapBagM_ (reportImplic ctxt2) implics

       -- whenNoErrs $ do (_, more_leftovers) <- tryReporters ctxt3 report3 suppressed_items
       --                 massertPpr (null more_leftovers) (ppr more_leftovers)
  where
    env = cec_tidy ctxt
    tidy_cts = bagToList (mapBag (tidyCt env) simples)

    suppress :: ErrorItem -> Bool
    suppress _ = False

    report1 = [ ("insoluble1", is_given_eq, False, ignoreErrorReporter)
              , ("insoluble2", utterly_wrong, True, mkGroupReporter mkEqErr)
              , ("skolem eq1", very_wrong, True, mkSkolReporter)
              , ("skolem eq2", skolem_eq, True, mkSkolReporter)
              , ("non-kv eq", non_kv_eq, True, mkSkolReporter)
              , ("Homo eqs", is_homo_equality, True, mkGroupReporter mkEqErr)
              ]

    report2 = [ ("Irreds", is_irred, False, mkGroupReporter mkIrredErr)
              , ("Rels", is_rel, False, mkGroupReporter mkRelErr)
              ]

    is_given_eq item pred
      | Given <- ei_flavor item
      , EqPred {} <- pred = True
      | otherwise = False

    utterly_wrong _ (EqPred k1 k2) = isRigidKi k1 && isRigidKi k2
    utterly_wrong _ _ = False

    very_wrong _ (EqPred k1 k2) = isSkolemKi tc_lvl k1 && isRigidKi k2
    very_wrong _ _ = False

    skolem_eq _ (EqPred k1 _) = isSkolemKi tc_lvl k1
    skolem_eq _ _ = False
    
    non_kv_eq _ (EqPred k1 _) = not (isKiVarKi k1)
    non_kv_eq _ _ = False
    
    is_homo_equality _ (EqPred _ _) = True
    is_homo_equality _ _ = False
    
    is_rel _ (RelPred {}) = True
    is_rel _ _ = False
    
    is_irred _ (IrredPred {}) = True
    is_irred _ _ = False

isSkolemKi :: TcLevel -> AnyMonoKind -> Bool
isSkolemKi tc_lvl ki
  | Just kv <- getKiVar_maybe ki
  = panic "isSkolemVar kv"
    || (panic "isTcVarVar kv && isTouchableMetaVar tc_lvl kv")
  | otherwise
  = False

--------------------------------------------
--      Reporters
--------------------------------------------

type Reporter = SolverReportErrCtxt -> NonEmpty ErrorItem -> TcM ()

type ReporterSpec = (String, ErrorItem -> Pred AnyKiVar -> Bool, Bool, Reporter)

mkSkolReporter :: Reporter
mkSkolReporter ctxt items = mapM_ (reportGroup mkEqErr ctxt) (group (toList items))
  where
    group [] = []
    group (item:items) = (item :| yeses) : group noes
      where
        (yeses, noes) = partition (group_with item) items

    group_with item1 item2
      | EQ <- cmp_loc item1 item2 = True
      | eq_lhs_kind item1 item2 = True
      | otherwise = False

zonkTidyTcLclEnvs :: AnyTidyEnv -> [CtLocEnv] -> ZonkM (AnyTidyEnv, NameEnv AnyType)
zonkTidyTcLclEnvs tidy_env lcls = foldM go (tidy_env, emptyNameEnv) (concatMap ctl_bndrs lcls)
  where
    go envs tc_bndr = case tc_bndr of
      TcTvBndr {} -> return envs
      TcKvBndr {} -> return envs
      TcIdBndr id _ -> panic "go_one (idName id) (idType id) envs"
      TcIdBndr_ExpType name et _ -> panic "zonkTidyTcLclEnvs TcIdBndr_ExpType" --do
        -- mb_ty <- liftIO $ readExpType_maybe et
        -- case mb_ty of
        --   Just ty -> panic go_one name ty envs
        --   Nothing -> return envs

    -- go_one name ty (tidy_env, name_env) = do
    --   if name `elemNameEv` name_env
    --     then return (tidy_env, name_env)
    --     else do (tidy_env', tidy_ty) <- zonkTidyTcType tidy_env ty
    --             return 

ignoreErrorReporter :: Reporter
ignoreErrorReporter ctxt items = do
  traceTc "mkGivenErrorReporter no" (ppr items $$ ppr (cec_encl ctxt))
  return ()

mkGroupReporter :: (SolverReportErrCtxt -> NonEmpty ErrorItem -> TcM SolverReport) -> Reporter
mkGroupReporter mk_err ctxt items
  = mapM_ (reportGroup mk_err ctxt) (equivClasses cmp_loc (toList items))

eq_lhs_kind :: ErrorItem -> ErrorItem -> Bool
eq_lhs_kind item1 item2
  = case (classifyPredKind (errorItemPred item1), classifyPredKind (errorItemPred item2)) of
      (EqPred k1 _, EqPred k2 _) -> k1 `eqMonoKind` k2
      _ -> pprPanic "mkSkolReporter" (ppr item1 $$ ppr item2)

cmp_loc :: ErrorItem -> ErrorItem -> Ordering
cmp_loc item1 item2 = get item1 `compare` get item2
  where
    get ei = realSrcSpanStart (ctLocSpan (errorItemCtLoc ei))

reportGroup :: (SolverReportErrCtxt -> NonEmpty ErrorItem -> TcM SolverReport) -> Reporter
reportGroup mk_err ctxt items = do
  err <- mk_err ctxt items
  traceTc "About to maybeReportErr"
    $ vcat [ text "Constraint:" <+> ppr items
           , text "cec_suppress =" <+> ppr (cec_suppress ctxt)
           , text "cec_defer_type_errors =" <+> ppr (cec_defer_type_errors ctxt) ]
  maybeReportError ctxt items err
  traceTc "reportGroup" (ppr items)
  mapM_ (addDeferredBinding ctxt err) items

nonDeferrableOrigin :: CtOrigin -> Bool
nonDeferrableOrigin OccurrenceOf {} = False
nonDeferrableOrigin KindEqOrigin {} = False
nonDeferrableOrigin GivenOrigin {} = False
nonDeferrableOrigin TupleTyOrigin = False

maybeReportError :: SolverReportErrCtxt -> NonEmpty ErrorItem -> SolverReport -> TcM ()
maybeReportError ctxt items@(item1 :| _) (SolverReport { sr_important_msg = important
                                                       , sr_supplementary = supp })
  = unless (cec_suppress ctxt || all ei_suppress items) $ do
  let reason | any (nonDeferrableOrigin . errorItemOrigin) items = ErrorWithoutFlag
             | otherwise = cec_defer_type_errors ctxt
      diag = TcRnSolverReport important reason
  msg <- mkErrorReport (ctLocEnv (errorItemCtLoc item1)) diag (Just ctxt) supp
  reportDiagnostic msg

addDeferredBinding :: SolverReportErrCtxt -> SolverReport -> ErrorItem -> TcM ()
addDeferredBinding ctxt err (EI { ei_evdest = Just dest, ei_pred = item_ki, ei_loc = loc })
  | deferringAnyBindings ctxt
  = panic "addDeferredBinding"
addDeferredBinding _ _ _ = return ()

tryReporters
  :: SolverReportErrCtxt
  -> [ReporterSpec]
  -> [ErrorItem]
  -> TcM (SolverReportErrCtxt, [ErrorItem])
tryReporters ctxt reporters items = do
  let (vis_items, invis_items) = partition (isVisibleOrigin . errorItemOrigin) items
  traceTc "tryReporters {" (ppr vis_items $$ ppr invis_items)
  (ctxt', items') <- go ctxt reporters vis_items invis_items
  traceTc "tryReporters }" (ppr items')
  return (ctxt', items')
  where
    go ctxt [] vis_items invis_items = return (ctxt, vis_items ++ invis_items)
    go ctxt (r:rs) vis_items invis_items = do
      (ctxt', vis_items') <- tryReporter ctxt r vis_items
      (ctxt'', invis_items') <- tryReporter ctxt' r invis_items
      go ctxt'' rs vis_items' invis_items'

tryReporter
  :: SolverReportErrCtxt
  -> ReporterSpec
  -> [ErrorItem]
  -> TcM (SolverReportErrCtxt, [ErrorItem])
tryReporter ctxt (str, keep_me, suppress_after, reporter) items = case nonEmpty yeses of
  Nothing -> pure (ctxt, items)
  Just yeses -> do
    traceTc "tryReporter {" (text str <+> ppr yeses)
    (_, no_errs) <- askNoErrs (reporter ctxt yeses)
    let suppress_now = not no_errs && suppress_after
        ctxt' = ctxt { cec_suppress = suppress_now || cec_suppress ctxt }
    traceTc "tryReporter env }" (text str <+> ppr (cec_suppress ctxt) <+> ppr suppress_after)
    return (ctxt', nos)
  where
    (yeses, nos) = partition keep items
    keep item = keep_me item (classifyPredKind (errorItemPred item))

mkErrorReport
  :: CtLocEnv
  -> TcRnMessage
  -> Maybe SolverReportErrCtxt
  -> [SolverReportSupplementary]
  -> TcM (MsgEnvelope TcRnMessage)
mkErrorReport tcl_env msg mb_ctxt supplementary = do
  mb_context <- traverse (\ctxt -> mkErrInfo (cec_tidy ctxt) (ctl_ctxt tcl_env)) mb_ctxt
  unit_state <- cs_units <$> getTopEnv
  hfdc <- getHoleFitDispConfig
  let err_info = ErrInfo
                 (fromMaybe empty mb_context)
                 (vcat $ map (pprSolverReportSupplementary hfdc) supplementary)
      detailed_msg = mkDetailedMessage err_info msg
  mkTcRnMessage (RealSrcSpan (ctl_loc tcl_env) Strict.Nothing)
                (TcRnMessageWithInfo unit_state $ detailed_msg)

pprSolverReportSupplementary :: HoleFitDispConfig -> SolverReportSupplementary -> SDoc
pprSolverReportSupplementary _ (SupplementaryBindings binds) = pprRelevantBindings binds
pprSolverReportSupplementary hfdc (SupplementaryHoleFits fits) = pprValidHoleFits hfdc fits
pprSolverReportSupplementary _ (SupplementaryCts cts) = pprConstraintsInclude cts

pprValidHoleFits :: HoleFitDispConfig -> ValidHoleFits -> SDoc
pprValidHoleFits _ _ = panic "pprValidHoleFits"

pprConstraintsInclude :: [(AnyPredKind, RealSrcSpan)] -> SDoc
pprConstraintsInclude _ = panic "pprConstraintsInclude"

{- *********************************************************************
*                                                                      *
                Irreducible predicate errors
*                                                                      *
********************************************************************* -}

mkIrredErr :: SolverReportErrCtxt -> NonEmpty ErrorItem -> TcM SolverReport
mkIrredErr ctxt items = panic "mkIrredErr"

{- *********************************************************************
*                                                                      *
                Equality errors
*                                                                      *
********************************************************************* -}

mkEqErr :: SolverReportErrCtxt -> NonEmpty ErrorItem -> TcM SolverReport
mkEqErr ctxt items
  | item1 :| _ <- tryFilter (not . ei_suppress) items
  = mkEqErr1 ctxt item1

mkEqErr1 :: SolverReportErrCtxt -> ErrorItem -> TcM SolverReport
mkEqErr1 ctxt item = do
  (ctxt, binds, item) <- relevantBindings True ctxt item
  traceTc "mkEqErr1" (ppr item $$ pprCtOrigin (errorItemOrigin item))
  let (ki1, ki2) = getKiEqPredKis (errorItemPred item)
  err_msg <- mkEqErr_help ctxt item ki1 ki2
  let report = add_relevant_bindings binds $ important ctxt err_msg
  return report

mkEqErr_help :: SolverReportErrCtxt -> ErrorItem -> AnyMonoKind -> AnyMonoKind -> TcM TcSolverReportMsg
mkEqErr_help ctxt item ki1 ki2
  | Just kv1 <- getKiVar_maybe ki1
  = mkKiVarEqErr ctxt item kv1 ki2
  | Just kv2 <- getKiVar_maybe ki2
  = mkKiVarEqErr ctxt item kv2 ki1
  | otherwise
  = reportEqErr ctxt item ki1 ki2

reportEqErr :: SolverReportErrCtxt -> ErrorItem -> AnyMonoKind -> AnyMonoKind -> TcM TcSolverReportMsg
reportEqErr ctxt item ki1 ki2 = do
  kv_info <- case getKiVar_maybe ki2 of
               Nothing -> return Nothing
               Just kv2 -> Just <$> extraKiVarEqInfo (panic "kv2, Nothing") ki1
  return $ Mismatch { mismatchMsg = mismatch
                    , mismatchKiVarInfo = kv_info
                    , mismatchAmbiguityInfo = [] }
  where
    mismatch = misMatchOrCND ctxt item ki1 ki2

mkKiVarEqErr
  :: SolverReportErrCtxt
  -> ErrorItem
  -> AnyKiVar
  -> AnyMonoKind
  -> TcM TcSolverReportMsg
mkKiVarEqErr ctxt item kv1 ki2 = do
  traceTc "mkKiVarEqErr" (ppr item $$ ppr kv1 $$ ppr ki2)
  mkKiVarEqErr' ctxt item kv1 ki2

mkKiVarEqErr'
  :: SolverReportErrCtxt
  -> ErrorItem
  -> AnyKiVar
  -> AnyMonoKind
  -> TcM TcSolverReportMsg
mkKiVarEqErr' ctxt item kv1 ki2
  = let headline_msg = misMatchOrCND ctxt item ki1 ki2
        mismatch_msg = mkMismatchMsg item ki1 ki2

        mb_concrete_reason
          | Just frr_orig <- panic "isConcreteVar_maybe kv1"
          = panic "mkKiVarEqErr'/concrete ki var"
          | Just (kv2, frr_orig) <- isConcreteKiVarKi_maybe ki2
          = panic "mkKiVarEqErr'/concrete kivarki"
          | otherwise
          = Nothing

        check_eq_result = case ei_m_reason item of
                            Just (NonCanonicalReason result) -> result
                            _ -> ctkeOK

        ki1 = mkKiVarKi kv1

    in if | Just frr_info <- mb_concrete_reason
            -> panic "mkKiVarEqErr'1"
          | check_eq_result `ctkerHasProblem` ctkeImpredicative
            -> do kivar_eq_info <- extraKiVarEqInfo (panic "kv1, Nothing") ki2
                  let poly_msg = CannotUnifyWithPolykind item kv1 ki2 mb_kv_info
                      mb_kv_info | panic "isSkolemVar kv1" = Just kivar_eq_info
                                 | otherwise = Nothing
                      main_msg = CannotUnifyKiVariable
                                 { mismatchMsg = headline_msg
                                 , cannotUnifyReason = poly_msg }
                  return main_msg

          | panic "isSkolemVar kv1"
            || panic "isTcVarVar kv1 && not (isKiVarKi ki2)"
            -> do kv_extra <- extraKiVarEqInfo (panic "kv1, Nothing") ki2
                  let reason = DifferentKiVars kv_extra
                      main_msg = CannotUnifyKiVariable
                                 { mismatchMsg = headline_msg
                                 , cannotUnifyReason = reason }
                  return main_msg
          | kv1 `elemVarSet` varsOfMonoKind ki2
            -> let ambiguity_infos = panic "kiEqInfoMsgs ki1 ki2"

                   occurs_err = OccursCheck { occursCheckAmbiguityInfos = ambiguity_infos }
                   main_msg = CannotUnifyKiVariable
                              { mismatchMsg = headline_msg
                              , cannotUnifyReason = occurs_err }
               in return main_msg

          | (implic:_) <- cec_encl ctxt
          , Implic { ic_skols = skols } <- implic
          , panic "kv1 `elem` skols"
            ->  do panic "mkKiVarEqErr'/skols in implic"
          
          | (implic:_) <- cec_encl ctxt
          , Implic { ic_skols = skols } <- implic
          , let esc_skols = panic "filter (`elemVarSet` (varsOfMonoKind ki2)) skols"
          , not (panic "null esc_skols")
            ->  panic "mkKiVarEqErr'/skols in implic 2"

          | (implic:_) <- cec_encl ctxt
          , Implic { ic_tclvl = lvl } <- implic
          -> panic "assertPpr (not (isTouchableMetaVar lvl kv1)) (ppr kv1 $$ ppr lvl)" $ do
              kv_extra <- extraKiVarEqInfo (panic "kv1, Just implic") ki2
              let kv_extra' = kv_extra { thisKiVarIsUntouchable = Just implic }
                  msg = Mismatch { mismatchMsg = mismatch_msg
                                 , mismatchKiVarInfo = Just kv_extra'
                                 , mismatchAmbiguityInfo = [] }
              return msg

          | otherwise
            -> reportEqErr ctxt item (mkKiVarKi kv1) ki2

kiEqInfoMsgs :: TcMonoKind -> TcMonoKind -> [AmbiguityInfo]
kiEqInfoMsgs ki1 ki2 = panic "kiEqInfoMsgs"

misMatchOrCND :: SolverReportErrCtxt -> ErrorItem -> AnyMonoKind -> AnyMonoKind -> MismatchMsg
misMatchOrCND ctxt item ki1 ki2
  | insoluble_item
    || (isRigidKi ki1 && isRigidKi ki2)
    || (ei_flavor item == Given)
    || null givens
  = mkMismatchMsg item ki1 ki2
  | otherwise
  = CouldNotDeduce givens (item :| []) (Just $ CND_Extra level ki1 ki2)
  where
    insoluble_item = case ei_m_reason item of
                       Nothing -> False
                       Just r -> isInsolubleReason r
    level = ctLocTypeOrKind_maybe (errorItemCtLoc item) `orElse` KindLevel
    givens = [ given | given <- getUserGivens ctxt, ic_given_eqs given /= NoGivenEqs ]

extraKiVarEqInfo :: (TcKiVar, Maybe Implication) -> AnyMonoKind -> TcM KiVarInfo
extraKiVarEqInfo (kv1, mb_implic) ki2 = do
  kv1_info <- extraKiVarInfo kv1
  ki2_info <- panic "ki_extra ki2"
  return $ KiVarInfo { thisKiVar = panic "kv1_info"
                     , thisKiVarIsUntouchable = mb_implic
                     , otherKi = panic "ki2_info" }
  where
    ki_extra ki = case getKiVar_maybe ki of
                    Just kv -> Just <$> extraKiVarInfo kv
                    Nothing -> return Nothing

extraKiVarInfo :: TcKiVar -> TcM TcKiVar
extraKiVarInfo kv = 
  case tcVarDetails kv of
    SkolemVar skol_info lvl -> do
      new_skol_info <- liftZonkM $ zonkSkolemInfo skol_info
      return $ mkTcKiVar (varName kv) (SkolemVar new_skol_info lvl)
    _ -> return kv
 
mkMismatchMsg :: ErrorItem -> AnyMonoKind -> AnyMonoKind -> MismatchMsg
mkMismatchMsg item ki1 ki2 = case orig of
  KindEqOrigin { keq_actual = keq_actual, keq_expected = keq_expected, keq_thing = mb_thing }
    -> KindEqMismatch { keq_mismatch_item = item
                      , keq_mismatch_ki1 = ki1
                      , keq_mismatch_ki2 = ki2
                      , keq_mismatch_actual = panic "keq_actual"
                      , keq_mismatch_expected = panic "keq_expected"
                      , keq_mismatch_what = mb_thing
                      , keq_mb_same_kicon = mb_same_kicon }
  _ -> BasicMismatch { mismatch_ea = NoEA
                     , mismatch_item = item
                     , mismatch_ki1 = ki1
                     , mismatch_ki2 = ki2
                     , mismatch_whenMatching = Nothing
                     , mismatch_mb_same_kicon = mb_same_kicon }
  where
    orig = errorItemOrigin item
    mb_same_kicon = sameKiConExtras ki2 ki1

sameKiConExtras :: AnyMonoKind -> AnyMonoKind -> Maybe SameKiConInfo
sameKiConExtras (KiConApp kc1 _) (KiConApp kc2 _)
  | kc1 == kc2 = Just $ SameKiCon kc1
sameKiConExtras (FunKi {}) (FunKi {}) = Just $ SameFunKi
sameKiConExtras _ _ = Nothing

      
  

{- *********************************************************************
*                                                                      *
                 Kind relation errors
*                                                                      *
********************************************************************* -}

mkRelErr
  :: HasDebugCallStack
  => SolverReportErrCtxt
  -> NonEmpty ErrorItem
  -> TcM SolverReport
mkRelErr ctxt orig_items =
  let items = tryFilter (not . ei_suppress) orig_items

      no_givens = null (getUserGivens ctxt)

      mk_minimal = mkMinimalBy errorItemPred . toList

      min_items = mk_minimal items
  in do err <- mk_rel_err ctxt (head min_items)
        return $ important ctxt err

mk_rel_err :: HasCallStack => SolverReportErrCtxt -> ErrorItem -> TcM TcSolverReportMsg
mk_rel_err ctxt item = do
  (_, rel_binds, _) <- relevantBindings True ctxt item
  return $ cannot_resolve_msg item rel_binds

  where
    cannot_resolve_msg :: ErrorItem -> RelevantBindings -> TcSolverReportMsg
    cannot_resolve_msg  item binds = CannotResolveRelation item binds

{-**********************************************************************
*                                                                      *
                      Relevant bindings
*                                                                      *
**********************************************************************-}

relevantBindings
  :: Bool
  -> SolverReportErrCtxt
  -> ErrorItem
  -> TcM (SolverReportErrCtxt, RelevantBindings, ErrorItem)
relevantBindings want_filtering ctxt item = do
  traceTc "relevantBindings" (ppr item)
  let loc = errorItemCtLoc item
      lcl_env = ctLocEnv loc
  (env1, tidy_orig) <- liftZonkM $ zonkTidyOrigin (cec_tidy ctxt) (ctLocOrigin loc)

  let ct_fvs = varsOfMonoKind (errorItemPred item)

      loc' = setCtLocOrigin loc tidy_orig
      item' = item { ei_loc = loc' }

  (env2, lcl_name_cache) <- liftZonkM $ zonkTidyTcLclEnvs env1 [lcl_env]

  relev_bds <- panic "relevant_bindings want_filtering lcl_env lcl_name_cache ct_fvs"
  let ctxt' = ctxt { cec_tidy = env2 }
  return (ctxt', relev_bds, item')

relevant_bindings
  :: Bool
  -> CtLocEnv
  -> NameEnv TcType
  -> MkVarSet (TcKiCoVar TcKiVar)
  -> TcM RelevantBindings
relevant_bindings want_filtering lcl_env lcl_name_env ct_kvs = do
  dflags <- getDynFlags
  traceTc "relevant_bindings"
    $ vcat [ ppr ct_kvs
           , pprWithCommas id [ ppr id <+> colon <+> ppr (varType id)
                              | TcIdBndr id _ <- ctl_bndrs lcl_env ]
           , pprWithCommas id [ ppr id | TcIdBndr_ExpType id _ _ <- ctl_bndrs lcl_env ] ]
  go dflags (maxRelevantBinds dflags) emptyVarSet (RelevantBindings [] False)
    (removeBindingShadowing $ ctl_bndrs lcl_env)

  where
    run_out :: Maybe Int -> Bool
    run_out Nothing = False
    run_out (Just n) = n <= 0

    dec_max :: Maybe Int -> Maybe Int
    dec_max = fmap (\n -> n - 1)

    go
      :: DynFlags
      -> Maybe Int
      -> AnyTyVarSet AnyKiVar
      -> RelevantBindings
      -> [TcBinder]
      -> TcM RelevantBindings
    go _ _ _ (RelevantBindings bds discards) []
      = return $ RelevantBindings (reverse bds) discards
    go dflags n_left tvs_seen rels@(RelevantBindings bds discards) (tc_bndr : tc_bndrs)
      = case tc_bndr of
          TcTvBndr {} -> discard_it
          TcKvBndr {} -> discard_it
          TcIdBndr id top_lvl -> panic "go2 (idName id) top_lvl"
          TcIdBndr_ExpType name et top_lvl -> panic "relevant_bindings TcIdBndr_ExpType"
      where
        discard_it = go dflags n_left tvs_seen rels tc_bndrs

        -- go2 id_name top_lvl = do
        --   let tidy_ty = case lookupNameEnv lcl_name_env id_name of
        --                   Just tty -> tty
        --                   Nothing -> pprPanic "relevant_bindings" (ppr id_name)
        --   traceTc "relevantBindings 1" (ppr id_name <+> colon <+> ppr tidy_ty)
        --   let id_tvs = tyVarsOfType tidy_ty
        --       bd = (id_name, tidy_ty)
        --       new_seen = tvs_seen `unionVarSet` id_tvs

        --   if | (want_filtering && not (hasPprDebug dflags)
        --         && id_tvs `disjointVarSet` ct_kvs)
        --        ->  discard_it
        --      | isTopLevel top_lvl && not (isNothing n_left)
        --        -> discard_it
        --      | run_out n_left && id_tvs `subVarSet` tvs_seen
        --        -> go dflags n_left tvs_seen (RelevantBindings bds True) tc_bndrs
        --      | otherwise
        --        -> go dflags (dec_max n_left) new_seen
        --              (RelevantBindings (bd:bds) discards) tc_bndrs

{-**********************************************************************
*                                                                      *
                     helper functions
*                                                                      *
**********************************************************************-}

tryFilter :: (a -> Bool) -> NonEmpty a -> NonEmpty a
tryFilter f as = fromMaybe as $ nonEmpty (filter f (toList as))
