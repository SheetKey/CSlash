module CSlash.Tc.Gen.Head where

-- import {-# SOURCE #-} GHC.Tc.Gen.Expr( tcExpr, tcCheckPolyExprNC, tcPolyLExprSig )

import CSlash.Cs
-- import CSlash.Cs.Syn.Type

import CSlash.Tc.Gen.CsType
-- import GHC.Tc.Gen.Bind( chooseInferredQuantifiers )
-- import GHC.Tc.Gen.Sig( tcUserTypeSig, tcInstSig )
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.Unify
import CSlash.Tc.Utils.Instantiate
import CSlash.Tc.Errors.Types
-- import GHC.Tc.Solver          ( InferMode(..), simplifyInfer )
import CSlash.Tc.Utils.Env
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.Constraint( WantedTyConstraints )
import CSlash.Tc.Utils.TcType as TcType
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Zonk.TcType

-- import CSlash.Core.UsageEnv      ( singleUsageUE, UsageEnv )
import CSlash.Core.ConLike( ConLike(..) )
import CSlash.Core.DataCon
import CSlash.Core.TyCon
import CSlash.Core.Type.Rep
import CSlash.Core.Type

import CSlash.Types.Id
import CSlash.Types.Id.Info
import CSlash.Types.Name
import CSlash.Types.Name.Reader
import CSlash.Types.SrcLoc
import CSlash.Types.Basic
import CSlash.Types.Error

import CSlash.Builtin.Names

import CSlash.Driver.DynFlags
import CSlash.Utils.Misc
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic

import CSlash.Data.Maybe
import Control.Monad
import CSlash.Rename.Unbound (WhatLooking(WL_Anything))

{- *********************************************************************
*                                                                      *
             Misc utility functions
*                                                                      *
********************************************************************* -}

addExprCtxt :: CsExpr Rn -> TcRn a -> TcRn a
addExprCtxt e thing_inside = case e of
  CsUnboundVar {} -> thing_inside
  _ -> addErrCtxt (exprCtxt e) thing_inside

exprCtxt :: CsExpr Rn -> SDoc
exprCtxt expr = hang (text "In the expression:") 2 (ppr (stripParensCsExpr expr))
