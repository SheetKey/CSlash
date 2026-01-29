module CSlash.CsToCore.Monad
  ( DsM
  , module CSlash.CsToCore.Monad
  ) where

import CSlash.Driver.Env
import CSlash.Driver.DynFlags
import CSlash.Driver.Ppr
import CSlash.Driver.Config.Diagnostic

import CSlash.Cs

import CSlash.CsToCore.Types
import CSlash.CsToCore.Errors.Types
-- import GHC.HsToCore.Pmc.Solver.Types (Nablas, initNablas)

import CSlash.Core
-- import GHC.Core.Make  ( unitExpr )
-- import GHC.Core.Utils ( exprType )
import CSlash.Core.DataCon
import CSlash.Core.ConLike
import CSlash.Core.TyCon
import CSlash.Core.Type
import CSlash.Core.Kind

import CSlash.IfaceToCore

import CSlash.Tc.Utils.Monad

import CSlash.Builtin.Names

import CSlash.Data.FastString

import CSlash.Unit.Env
import CSlash.Unit.External
import CSlash.Unit.Module
import CSlash.Unit.Module.ModGuts

import CSlash.Types.Name.Reader
import CSlash.Types.SourceFile
import CSlash.Types.Var.Id
-- import CSlash.Types.Var (EvId)
import CSlash.Types.SrcLoc
import CSlash.Types.TypeEnv
import CSlash.Types.Unique.Supply
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Ppr
-- import CSlash.Types.Literal ( mkLitString )
-- import GHC.Types.CostCentre.State
import CSlash.Types.TyThing
import CSlash.Types.Error
import CSlash.Types.CompleteMatch
import CSlash.Types.Unique.DSet

-- import CSlash.Tc.Utils.Env (lookupGlobal)

import CSlash.Utils.Error
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import qualified CSlash.Data.Strict as Strict

import Data.IORef
import CSlash.Driver.Env.KnotVars
import qualified Data.Set as S
import GHC.IO.Unsafe (unsafeInterleaveIO)

{- *********************************************************************
*                                                                      *
                Data types for the desugarer
*                                                                      *
********************************************************************* -}
