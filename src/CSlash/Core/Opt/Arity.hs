module CSlash.Core.Opt.Arity where

import CSlash.Cs.Pass

import CSlash.Core as Core
-- import CSlash.Core.FVs
import CSlash.Core.Utils
import CSlash.Core.DataCon
import CSlash.Core.TyCon     ( TyCon, tyConArity, isInjectiveTyCon )
-- import CSlash.Core.TyCon.RecWalk     ( initRecTc, checkRecTc )

import CSlash.Core.Subst
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.Type.Compare( eqType )

import CSlash.Types.Demand
-- import CSlash.Types.Cpr( CprSig, mkCprSig, botCpr )
import CSlash.Types.Var.Id
import CSlash.Types.Var
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Basic
import CSlash.Types.Tickish

import CSlash.Builtin.Types.Prim
import CSlash.Builtin.Uniques

import CSlash.Data.FastString
-- import CSlash.Data.Graph.UnVar
import CSlash.Data.Pair

import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc

import Data.List.NonEmpty ( nonEmpty )
import qualified Data.List.NonEmpty as NE
import Data.Maybe( isJust )

joinRhsArity :: CoreExpr -> JoinArity
joinRhsArity (Lam _ _ e) = 1 + joinRhsArity e
joinRhsArity _ = 0

{- *********************************************************************
*                                                                      *
              typeArity
*                                                                      *
********************************************************************* -}

isOneShotBndr :: CoreBndr Zk -> Bool
isOneShotBndr Tv{} = True
isOneShotBndr KCv{} = True -- TODO: double check
isOneShotBndr Kv{} = True
isOneShotBndr (Core.Id id) = idOneShotInfo id == OneShotLam

{- *********************************************************************
*                                                                      *
              The main eta-expander
*                                                                      *
********************************************************************* -}

etaExpand :: Arity -> CoreExpr -> CoreExpr
etaExpand n orig_expr = panic "exa_expand in_scope (replicate n NoOneShotInfo) orig_expr"
  -- where
  --   in_scope = {-# SCC "eta_expand:in-scopeX" #-}
  --              panic "mkTermInScopeSets (exprFreeVars orig_expr)"
