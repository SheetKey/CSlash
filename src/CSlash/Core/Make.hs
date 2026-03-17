module CSlash.Core.Make where

import CSlash.Cs.Pass

import CSlash.Types.Var
import CSlash.Types.Var.Id
import CSlash.Types.TyThing
import CSlash.Types.Var.Id.Info
import CSlash.Types.Demand
import CSlash.Types.Name hiding (varName)
import CSlash.Types.Literal
import CSlash.Types.Unique.Supply

import CSlash.Core as Core
import CSlash.Core.Utils
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.Predicate
import CSlash.Core.Type.Compare
import CSlash.Core.DataCon
import CSlash.Core.Kind

import CSlash.Builtin.Types
import CSlash.Builtin.Types.Prim
import CSlash.Builtin.Names

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic

import CSlash.Settings.Constants
import CSlash.Data.FastString
import CSlash.Data.Maybe

import Data.List (partition)
import Data.List.NonEmpty (NonEmpty(..))
import Data.Char (ord)

{-**********************************************************************
*                                                                      *
           Basic Core Construction
*                                                                      *
**********************************************************************-}

mkCoreLams :: [(CoreBndr Zk, Maybe (MonoKind Zk))] -> CoreExpr -> CoreExpr
mkCoreLams bndrs body = foldr (uncurry Lam) body bndrs 

infixl 4`mkCoreApps`
mkCoreApps :: CoreExpr -> [CoreExpr] -> CoreExpr
mkCoreApps fun args = fst $ foldl' (mkCoreAppTyped doc_string) (fun, fun_ty) args
  where
    doc_string = ppr fun_ty $$ ppr fun $$ ppr args
    fun_ty = exprType fun

infixl 4 `mkCoreApp`
mkCoreApp :: SDoc -> CoreExpr -> CoreExpr -> CoreExpr
mkCoreApp s fun arg = fst $ mkCoreAppTyped s (fun, exprType fun) arg

mkCoreAppTyped :: SDoc -> (CoreExpr, Type Zk) -> CoreExpr -> (CoreExpr, Type Zk)
mkCoreAppTyped _ (fun, fun_ty) (Type ty)
  = (App fun (Type ty), piResultTy fun_ty ty)
mkCoreAppTyped _ (fun, fun_ty) (KiCo kco)
  = (App fun (KiCo kco), piResultTy fun_ty (KindCoercion kco))
mkCoreAppTyped _ (fun, fun_ty) (Kind ki)
  = (App fun (Kind ki), piResultTy fun_ty (Embed ki))
mkCoreAppTyped d (fun, fun_ty) arg
  = assertPpr (isFunTy fun_ty) (ppr fun $$ ppr arg $$ d)
    (App fun arg, funResultTy fun_ty)

{-**********************************************************************
*                                                                      *
           Building case expressions
*                                                                      *
**********************************************************************-}

mkWildValBinder :: Type Zk -> Id Zk
mkWildValBinder ty = mkLocalId wildCardName ty

mkWildCase :: CoreExpr -> Type Zk -> Type Zk -> [CoreAlt] -> CoreExpr
mkWildCase scrut scrut_ty res_ty alts
  = Case scrut (Core.Id $ mkWildValBinder scrut_ty) res_ty alts

mkIfThenElse :: CoreExpr -> CoreExpr -> CoreExpr -> CoreExpr
mkIfThenElse guard then_expr else_expr
  = mkWildCase guard (exprType guard) (exprType then_expr)
    [ Alt (DataAlt falseDataCon) [] else_expr
    , Alt (DataAlt trueDataCon) [] then_expr ]

{-**********************************************************************
*                                                                      *
           Floats
*                                                                      *
**********************************************************************-}

data FloatBind
  = FloatLet CoreBind
  | FloatCase CoreExpr (Id Zk) AltCon [CoreBndr Zk]

instance Outputable FloatBind where
  ppr (FloatLet b) = text "LET" <+> panic "ppr b"
  ppr (FloatCase e b c bs) = hang (text "CASE" <+> ppr e <+> text "of" <+> ppr b)
                             2 (ppr c <+> ppr bs)
