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
-- import {-# SOURCE #-} GHC.Tc.Errors.Hole ( findValidHoleFits, getHoleFitDispConfig, pprHoleFit )

import CSlash.Types.Name
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
import CSlash.Core.Type.Tidy
import CSlash.Core.Kind
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
import CSlash.Utils.FV ( fvVarList, unionFV )

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
       
       let free_kvs = kiVarsOfWCList wanted
           tidy_env = tidyFreeTyKiVars emptyTidyEnv free_kvs

       traceTc "reportUnsolved (after zonking):"
         $ vcat [ text "Free kivars:" <+> ppr free_kvs
                , text "Tidy env:" <+> ppr tidy_env
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
                                 , ic_wanted = wanted
                                 , ic_binds = evb
                                 , ic_status = status
                                 , ic_info = info
                                 , ic_env = ct_loc_env
                                 , ic_tclvl = tc_lvl }) = do
  traceTc "reportImplic"
    $ vcat [ text "tidy env:" <+> ppr (cec_tidy ctxt)
           , text "skols:" <+> ppr tvs
           , text "tidy skols:" <+> ppr tvs' ]

  when bad_telescope $ panic "reportBadTelescope ctxt ct_loc_ev info tvs"

  reportWanteds ctxt' tc_lvl wanted

  where
    insoluble = isInsolubleStatus status
    (env1, tvs') = tidyVarBndrs (cec_tidy ctxt) $ tvs

    info' = tidySkolemInfoAnon env1 info
    implic' = implic { ic_skols = tvs', ic_info = info' }

    ctxt1 = maybeSwitchOffDefer evb ctxt
    ctxt' = ctxt1 { cec_tidy = env1
                  , cec_encl = implic' : cec_encl ctxt
                  , cec_suppress = insoluble || cec_suppress ctxt
                  , cec_binds = evb  }

    bad_telescope = case status of
      IC_BadTelescope -> True
      _ -> False

mkErrorItem :: Ct -> TcM (Maybe ErrorItem)
mkErrorItem ct = do
  let loc = ctLoc ct
      flav = ctFlavor ct
  (suppress, m_evdest) <- case ctEvidence ct of
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

isSkolemKi :: TcLevel -> MonoKind -> Bool
isSkolemKi tc_lvl ki
  | Just kv <- getKiVarMono_maybe ki
  = isSkolemKiVar kv
    || (isKiVarKiVar kv && isTouchableMetaKiVar tc_lvl kv)
  | otherwise
  = False

--------------------------------------------
--      Reporters
--------------------------------------------

type Reporter = SolverReportErrCtxt -> NonEmpty ErrorItem -> TcM ()

type ReporterSpec = (String, ErrorItem -> Pred -> Bool, Bool, Reporter)

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
  hfdc <- panic "getHoleFitDispConfig"
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

pprConstraintsInclude :: [(PredKind, RealSrcSpan)] -> SDoc
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
mkEqErr ctxt items = panic "mkEqErr"

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
mkRelErr ctxt orig_items = panic "mkRelErr"
