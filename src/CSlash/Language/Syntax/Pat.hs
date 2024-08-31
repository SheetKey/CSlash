{-# LANGUAGE TypeFamilies #-}

module CSlash.Language.Syntax.Pat where

import {-# SOURCE #-} CSlash.Language.Syntax.Expr (SyntaxExpr)

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Lit
import CSlash.Language.Syntax.Type
import CSlash.Language.Syntax.Kind
import CSlash.Language.Syntax.Basic

type LPat p = XRec p (Pat p)

data Pat p
  ------------ Simple patterns ---------------
  = WildPat (XWildPat p)
  | VarPat (XVarPat p) (LIdP p)
  | TyVarPat (XTyVarPat p) (LIdP p)
  | AsPat (XAsPat p) (LIdP p) (LPat p)
  | ParPat (XParPat p) (LPat p)
  ------------ Tuples, sums ---------------
  | TuplePat (XTuplePat p) [LPat p]
  | SumPat (XSumPat p) (LPat p) ConTag SumWidth
  ------------ Constructor patterns ---------------
  | ConPat
    { pat_con_ext :: XConPat p
    , pat_con :: XRec p (ConLikeP p)
    , pat_args :: CsConPatDetails p
    }
  ------------ Literals ---------------
  | LitPat (XLitPat p) (CsLit p)
  | NPat (XNPat p) (XRec p (CsOverLit p)) (Maybe (SyntaxExpr p)) (SyntaxExpr p)
  ------------ With type signature ---------------
  | SigPat (XSigPat p) (LPat p) (CsPatSigType (NoTc p))
  | KdSigPat (XKdSigPat p) (LPat p) (CsPatSigKind (NoTc p))
  ------------ Implicit (Type) parameters ---------------
  | ImpPat (XImpPat p) (LPat p)

type family ConLikeP x

data CsConPatTyArg p = CsConPatTyArg !(XConPatTyArg p) (CsTyPat p)

type family XConPatTyArg p

type CsConPatDetails p = CsConDetails (CsConPatTyArg (NoTc p)) (LPat p)
