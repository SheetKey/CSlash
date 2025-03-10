module CSlash.Tc.Solver where

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
-- import CSlash.Tc.Errors
import CSlash.Tc.Errors.Types
-- import GHC.Tc.Types.Evidence
-- import GHC.Tc.Solver.Solve   ( solveSimpleGivens, solveSimpleWanteds )
-- import GHC.Tc.Solver.Dict    ( makeSuperClasses, solveCallStack )
-- import GHC.Tc.Solver.Rewrite ( rewriteType )
-- import GHC.Tc.Utils.Unify    ( buildTvImplication )
-- import GHC.Tc.Utils.TcMType as TcM
import CSlash.Tc.Utils.Monad   as TcM
import CSlash.Tc.Zonk.TcType     as TcM
import CSlash.Tc.Solver.InertSet
import CSlash.Tc.Solver.Monad  as TcS
import CSlash.Tc.Types.Constraint
-- import GHC.Tc.Instance.FunDeps
-- import GHC.Core.Predicate
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.TcType
import CSlash.Core.Type
import CSlash.Core.Ppr
import CSlash.Core.TyCon    ( TyConBinder{-, isTypeFamilyTyCon-} )
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

simplifyTop :: WantedConstraints -> TcM ()
simplifyTop wanteds = do
  traceTc "simplifyTop {" $ text "wanted = " <+> ppr wanteds
  ((final_wc, unsafe_ol), binds1) <- runTcS $ do
    final_wc <- simplifyTopWanteds wanteds
    unsafe_ol <- getSafeOverlapFailures
    return (final_wc, unsafe_ol)
  traceTc "End simplifyTop }" empty

  binds2 <- reportUnsolved final_wc

  traceTc "reportUnsolved (unsafe overlapping) {" empty
  unless (isEmptyBag unsafe_ol) $ do
    errs_var <- getErrsVar
    saved_msg <- TcM.readTcRef errs_var
    TcM.writeTcRef errs_var emptyMessages

    warnAllUnsolved

    whyUnsafe <- getWarningMessages <$> TcM.readTcRef errs_var
    TcM.writeTcRef errs_var saved_msg
    recordUnsafeInfer (mkMessages whyUnsafe)
  traceTc "reportUnsolved (unsafe overlapping) }" empty

  return (evBindsMapBinds binds1 `unionBags` binds2)

pushLevelAndSolveEqualities :: SkolemInfoAnon -> [TyConBinder] -> TcM a -> TcM a
pushLevelAndSolveEqualities skol_info_anon tcbs thing_inside = do
  (tclvl, wanted, res) <- pushLevelAndSolveEqualitiesX "pushLevelAndSolveEqualities" thing_inside
  report_unsolved_equalities skol_info_anon (binderVars tcbs) tclvl wanted
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
  :: SkolemInfoAnon -> [TcTyVar] -> TcLevel -> WantedConstraints -> TcM ()
report_unsolved_equalities skol_info_anon skol_tvs tclvl wanted
  | isEmptyWC wanted
  = return ()
  | otherwise
  = checkNoErrs $ do
      implic <- buildTvImplication skol_info_anon skol_tvs tclvl wanted
      reportAllUnsolved (mkImplicWC (unitBag implic))

simplifyTopWanteds :: WantedConstraints -> TcS WantedConstraints
simplifyTopWanteds wanteds = do
  wc_first_go <- nestTcS (solveWanteds wanteds)
  dflags <- getDynFlags
  wc_defaulted <- try_tyvar_defaulting dflags wc_first_go
  useUnsatisfiableGivens wc_defaulted
  where
    try_tyvar_defaulting :: DynFlags -> WantedConstraints -> TcS WantedConstraints
    try_tyvar_defaulting dflags wc
      | isEmptyWC wc
      = return wc
      | otherwise
      = do free_tvs <- TcS.zonkTyVarsAndFVList 

{- *********************************************************************
*                                                                      *
                      Main Simplifier
*                                                                      *
********************************************************************* -}
 
simplifyWanteds :: WantedConstraints -> TcS WantedConstraints
simplifyWanteds wc
  | isEmptyWC wc
  = return wc
  | otherwise
  = do cur_lvl <- TcS.getTcLevel
       traceTcS "solveWanteds {"
         $ vcat [ text "Level =" <+> ppr cur_lvl
                , ppr wc ]

       dflags <- getDynFlags
       solved_wc <- simplify_loop 0 (solverIterations dflags) True wc

       "unfinished"

simplify_loop :: Int -> IntWithInf -> Bool -> WantedConstraints -> TcS WantedConstraints
simplify_loop n limit redo_implications wc@(WC { wc_simple = simple, wc_impl = implics }) = do
  csTraceTcS $ text "simplify_loop iteration=" <> int n
               <+> (parens $ hsep [ text "definitely_redo ="
                                    <+> ppr redo_implications
                                    <> comma
                                  , int (lengthBag simples) <+> text "simples to solve" ])
  traceTcs "simplify_loop: wc =" (ppr wc)

  (unifs1, wc1) <- reportUnifications $ solveSimpleWanteds simples

  "unfinished"
