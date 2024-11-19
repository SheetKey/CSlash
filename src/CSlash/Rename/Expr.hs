{-# LANGUAGE ConstraintKinds #-}

module CSlash.Rename.Expr where

import CSlash.Data.FastString

import CSlash.Rename.Bind ( {-rnLocalBindsAndThen, rnLocalValBindsLHS, rnLocalValBindsRHS
                          , -}rnMatchGroup, rnGRHS, makeMiniFixityEnv)
import CSlash.Cs
import CSlash.Tc.Errors.Types
-- import GHC.Tc.Utils.Env ( isBrackStage )
import CSlash.Tc.Utils.Monad
import CSlash.Unit.Module ( getModule )
import CSlash.Rename.Env
import CSlash.Rename.Fixity
import CSlash.Rename.Utils
  ( bindLocalNamesFV, checkDupNames
  , bindLocalNames
  {-, mapMaybeFvRn-}, mapFvRn
  , warnUnusedLocalBinds{-, typeAppErr-}
  , wrapGenSpan{-, genCsIntegralLit, genCsTyLit
  , genCsVar, genLCsVar, genCsApp, genCsApps, genCsApps'
  , genAppType, isIrrefutableCsPat-} )
-- import CSlash.Rename.Unbound ( reportUnboundName )
import CSlash.Rename.CsType
import CSlash.Rename.Pat
import CSlash.Driver.DynFlags
import CSlash.Builtin.Names
-- import CSlash.Builtin.Types ( nilDataConName )

import CSlash.Types.Basic (TypeOrKind (TypeLevel))
import CSlash.Types.Fixity
import CSlash.Types.Id.Make
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Name.Reader
import CSlash.Types.Unique.Set
import CSlash.Types.SourceText
import CSlash.Types.SrcLoc
import CSlash.Utils.Misc
import CSlash.Data.List.SetOps ( removeDupsOn )
import CSlash.Data.Maybe
import CSlash.Utils.Error
import CSlash.Utils.Panic
import CSlash.Utils.Outputable as Outputable

import Control.Monad
import Data.List (unzip4, minimumBy)
import Data.List.NonEmpty ( NonEmpty(..), nonEmpty )
import Control.Arrow (first)
import Data.Ord
import Data.Array
import qualified Data.List.NonEmpty as NE

{- *********************************************************************
*                                                                      *
              Expressions
*                                                                      *
********************************************************************* -}

rnLExpr :: LCsExpr Ps -> RnM (LCsExpr Rn, FreeVars)
rnLExpr = wrapLocFstMA rnExpr

rnExpr :: CsExpr Ps -> RnM (CsExpr Rn, FreeVars)
rnExpr _ = panic "rnExpr"

{- *********************************************************************
*                                                                      *
              Stmts
*                                                                      *
********************************************************************* -}

type RnStmtsAnnoBody body
  = ( Outputable (body Ps) )

rnStmts
  :: RnStmtsAnnoBody body
  => CsStmtContextRn
  -> (body Ps -> RnM (body Rn, FreeVars))
  -> [LStmt Ps (LocatedA (body Ps))]
  -> ([Name] -> RnM (thing, FreeVars))
  -> RnM (([LStmt Rn (LocatedA (body Rn))], thing), FreeVars)
rnStmts ctxt rnBody stmts thing_inside = do
  ((stmts', thing), fvs) <- rnStmtsWithFreeVars ctxt rnBody stmts thing_inside
  return ((map fst stmts', thing), fvs)

rnStmtsWithFreeVars
  :: RnStmtsAnnoBody body
  => CsStmtContextRn
  -> ((body Ps) -> RnM ((body Rn), FreeVars))
  -> [LStmt Ps (LocatedA (body Ps))]
  -> ([Name] -> RnM (thing, FreeVars))
  -> RnM (([(LStmt Rn (LocatedA (body Rn)), FreeVars)], thing), FreeVars)
rnStmtsWithFreeVars ctxt _ [] thing_inside = do
  checkEmptyStmts ctxt
  (thing, fvs) <- thing_inside []
  return (([], thing), fvs)
rnStmtsWithFreeVars _ _ _ _ = panic "rnStmtsWithFreeVars"

{- *********************************************************************
*                                                                      *
      Errors
*                                                                      *
********************************************************************* -}

checkEmptyStmts :: CsStmtContextRn -> RnM ()
checkEmptyStmts ctxt = panic "checkEmptyStmts"
