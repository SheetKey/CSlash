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
-- import GHC.Tc.Solver.InertSet
-- import GHC.Tc.Solver.Monad  as TcS
-- import GHC.Tc.Types.Constraint
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

pushLevelAndSolveEqualities :: SkolemInfoAnon -> [TyConBinder] -> TcM a -> TcM a
pushLevelAndSolveEqualities skol_info_anon tcbs thing_inside = do
  (_, res) <- pushLevelAndSolveEqualitiesX "pushLevelAndSolveEqualities" thing_inside
  return res

pushLevelAndSolveEqualitiesX :: String -> TcM a -> TcM (TcLevel, a)
pushLevelAndSolveEqualitiesX callsite thing_inside = do
  traceTc "pushLevelAndSolveEqualitiesX {" (text "Called from" <+> text callsite)
  (tclvl, res) <- pushTcLevelM thing_inside
  traceTc "pushLevelAndSolveEqualities }" (vcat [ text "Level:" <+> ppr tclvl ])
  return (tclvl, res)

