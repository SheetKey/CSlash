module CSlash.Tc.Gen.App where

import {-# SOURCE #-} CSlash.Tc.Gen.Expr( tcPolyExpr )

import CSlash.Cs

import CSlash.Tc.Gen.Head
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.Unify
import CSlash.Tc.Utils.Instantiate
import CSlash.Tc.Gen.CsType
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.TcType as TcType
import CSlash.Tc.Zonk.TcType

import CSlash.Core.ConLike (ConLike(..))
import CSlash.Core.DataCon ( dataConTyCon )
import CSlash.Core.TyCon
import CSlash.Core.Type.Rep
import CSlash.Core.Type.Ppr
-- import CSlash.Core.Type.Subst ( substTyWithInScope )
import CSlash.Core.Type
-- import GHC.Core.Coercion

import CSlash.Builtin.Names

import CSlash.Types.Var
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Reader
import CSlash.Types.SrcLoc
import CSlash.Types.Var.Env  ( emptyTidyEnv, mkInScopeSet )

import CSlash.Data.Maybe

import CSlash.Utils.Misc
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic

import Control.Monad
import Data.Function
import Data.Semigroup

{- *********************************************************************
*                                                                      *
              Typechecking n-ary applications
*                                                                      *
********************************************************************* -}

tcApp :: CsExpr Rn -> ExpRhoType -> TcM (CsExpr Tc)
tcApp rn_expr exp_res_ty = do
  panic "tcApp"
