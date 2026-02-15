module CSlash.Core.Utils where

import CSlash.Cs.Pass

import CSlash.Platform

import CSlash.Core as Core
import CSlash.Core.Ppr
-- import GHC.Core.FVs( bindFreeVars )
import CSlash.Core.DataCon
import CSlash.Core.Type as Type
-- import GHC.Core.Predicate( isEqPred )
import CSlash.Core.Type.Compare( eqType )
-- import GHC.Core.Coercion
import CSlash.Core.Reduction
import CSlash.Core.TyCon
import CSlash.Core.Kind

import CSlash.Types.Var
import CSlash.Types.SrcLoc
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Name
import CSlash.Types.Literal
import CSlash.Types.Tickish
import CSlash.Types.Var.Id.Info
import CSlash.Types.Basic( Arity )
import CSlash.Types.Unique
import CSlash.Types.Unique.Set
import CSlash.Types.Demand
-- import CSlash.Types.RepType (isZeroBitTy)

import CSlash.Data.FastString
import CSlash.Data.Maybe
import CSlash.Data.List.SetOps( minusList )
import CSlash.Data.OrdList

import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc

import Data.ByteString     ( ByteString )
import Data.Function       ( on )
import Data.List           ( sort, sortBy, partition, zipWith4, mapAccumL )
import qualified Data.List as Partial ( init, last )
import Data.Ord            ( comparing )
import Control.Monad       ( guard )
import qualified Data.Set as Set

{-**********************************************************************
*                                                                      *
           Type of a Core atom/expression
*                                                                      *
**********************************************************************-}

exprType :: HasDebugCallStack => CoreExpr -> Type Zk
exprType (Var var) = varType var
exprType (Lit lit) = literalType lit
exprType (Let bind body)
  | NonRec (Tv tv) rhs <- bind
  = panic "exprType"
  | NonRec (KCv kcv) rhs <- bind
  = panic "exprType"
  | NonRec (Kv kv) rhs <- bind
  = panic "exprType"
  | otherwise = exprType body
exprType (Case _ _ ty _) = ty
exprType (Cast _ co) = tycoercionRType co
exprType (Tick _ e) = exprType e
exprType (Lam bndr mki expr) = mkLamType bndr mki (exprType expr)
exprType e@(App _ _) = case collectArgs e of
                        (fun, args) -> applyTypeToArgs (exprType fun) args
exprType (Type ty) = pprPanic "exprType" (ppr ty)
exprType (KiCo kco) = pprPanic "exprType" (ppr kco)
exprType (Kind ki) = pprPanic "exprType" (ppr ki)

mkLamType :: HasDebugCallStack => CoreBndr Zk -> Maybe (MonoKind Zk) -> Type Zk -> Type Zk
mkLamType (Core.Id id) (Just ki) body_ty = mkFunctionType (varType id) ki body_ty
mkLamType (Tv tv) Nothing body_ty = mkForAllTy (Bndr tv coreTyLamForAllTyFlag) body_ty
mkLamType (KCv kcv) Nothing body_ty = mkForAllKiCo kcv body_ty
mkLamType (Kv kv) Nothing body_ty = mkBigLamTy kv body_ty
mkLamType bndr ki body = pprPanic "mkLamType bad CsLam"
                         $ vcat [ text "bndr" <+> ppr bndr
                                , text "maybe fun ki" <+> ppr ki
                                , text "body" <+> ppr body ]

applyTypeToArgs :: HasDebugCallStack => Type Zk -> [CoreExpr] -> Type Zk
applyTypeToArgs op_ty args = go op_ty args
  where
    go op_ty [] = op_ty
    go op_ty (Type ty : args) = go_ty_args op_ty [ty] args
    go op_ty (KiCo co : args) = go_ty_args op_ty [KindCoercion co] args
    go op_ty (Kind ki : args) = go_ty_args op_ty [Embed ki] args
    go op_ty (_ : args) | Just (_, _, res_ty) <- splitFunTy_maybe op_ty
                        = go res_ty args
    go _ args = pprPanic "applyTypeToArgs" (panic_msg args)

    go_ty_args op_ty rev_tys (Type ty : args)
      = go_ty_args op_ty (ty : rev_tys) args
    go_ty_args op_ty rev_tys (KiCo co : args)
      = go_ty_args op_ty (KindCoercion co : rev_tys) args
    go_ty_args op_ty rev_tys (Kind ki : args)
      = go_ty_args op_ty (Embed ki : rev_tys) args
    go_ty_args op_ty rev_tys args = go (piResultTys op_ty (reverse rev_tys)) args

    panic_msg as = vcat [ text "Type:" <+> ppr op_ty
                        , text "Args:" <+> ppr args
                        , text "Args':" <+> ppr as ]
