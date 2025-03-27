module CSlash.Tc.Errors where

import Prelude hiding ((<>))

-- import GHC.Driver.Env (hsc_units)
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
-- import CSlash.Tc.Zonk.Type
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Zonk.TcType
import CSlash.Tc.Types.Origin
-- import GHC.Tc.Types.Evidence
-- import GHC.Tc.Types.EvTerm
-- import GHC.Tc.Instance.Family
-- import GHC.Tc.Utils.Instantiate
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

-- import GHC.Core.Predicate
import CSlash.Core.Type
-- import GHC.Core.Coercion
import CSlash.Core.Type.Ppr ( pprTyVars )
-- import GHC.Core.InstEnv
import CSlash.Core.TyCon
import CSlash.Core.DataCon

import CSlash.Utils.Error (diagReasonSeverity,  pprLocMsgEnvelope )
import CSlash.Utils.Misc
import CSlash.Utils.Outputable as O
import CSlash.Utils.Panic
-- import CSlash.Utils.FV ( fvVarList, unionFV )

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

reportUnsolved :: WantedConstraints -> TcM ()
reportUnsolved wanted = do
  defer_errors <- goptM Opt_DeferTypeErrors
  let type_errors | not defer_errors = ErrorWithoutFlag
                  | otherwise = panic "reportUnsolved DeferTypeErrors"

  defer_holes <- goptM Opt_DeferTypedHoles
  let expr_holes | not defer_holes = ErrorWithoutFlag
                 | otherwise = panic "reportUnsolved DeferTypedHoles"

  defer_out_of_scope <- goptM Opt_DeferOutOfScopeVariables
  let out_of_scope_holes | not defer_out_of_scope = ErrorWithoutFlag
                         | otherwise = panic "reportUnsolved DeferOutOfScopeVariables"

  report_unsolved type_errors expr_holes out_of_scope_holes wanted

reportAllUnsolved :: WantedConstraints -> TcM ()
reportAllUnsolved wanted = panic "reportAllUnsolved"

report_unsolved
  :: DiagnosticReason
  -> DiagnosticReason
  -> DiagnosticReason
  -> WantedConstraints
  -> TcM ()
report_unsolved type_erros expr_holes out_of_scope_holes wanted
  | isEmptyWC wanted
  = return ()
  | otherwise = panic "report_unsolved"
  -- = do traceTc "reportUnsolved {" 
  --        $ vcat [ text "type errors:" <+> ppr type_errors
  --               , text "expr holes:" <+> ppr expr_holes
  --               , text "type holes:" <+> ppr type_holes
  --               , text "scope holes:" <+> ppr out_of_scope_holes ]
  --      traceTc "reportUnsolved (before zonking and tidying)" (ppr wanted)

  --      wanted <- liftZonkM $ zonkWC wanted
       
