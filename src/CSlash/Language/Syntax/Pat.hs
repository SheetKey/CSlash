{-# LANGUAGE TypeFamilies #-}

module CSlash.Language.Syntax.Pat where

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Lit
import CSlash.Language.Syntax.Type

type LPat p = XRec p (Pat p)

type ConTag = Int

type SumWidth = Int

data Pat p
  ------------ Simple patterns ---------------
  = WildPat (XWildPat p)
  | VarPat (XVarPat p) (LIdP p)
  ------------ Tuples, sums ---------------
  | TuplePat (XTuplePat p) [LPat p]
  | SumPat (XSumPat p) (LPat p) ConTag SumWidth
  ------------ Literals ---------------
  | LitPat (XLitPat p) (CsLit p)
  ------------ With type signature ---------------
  | SigPat (XSigPat p) (LPat p) (CsPatSigType (NoTc p))

data CsConPatTyArg p = CsConPatTyArg !(XConPatTyArg p) (CsTyPat p)

type family XConPatTyArg p
