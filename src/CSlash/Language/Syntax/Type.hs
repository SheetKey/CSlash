{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module CSlash.Language.Syntax.Type where

import {-# SOURCE #-} CSlash.Language.Syntax.Expr

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Kind
import CSlash.Types.Name.Reader

import Data.Data (Data)

type LCsType pass = XRec pass (CsType pass)

data CsPatSigType pass = CsPS
  { csps_ext :: XCsPS pass
  , csps_body :: LCsType pass
  }

data CsTyPat pass = CsTP
  { cstp_ext :: XCsTP pass
  , cstp_body :: LCsType pass
  }

type LCsTyPat pass = XRec pass (CsTyPat pass)

type LCsSigType pass = XRec pass (CsSigType pass)

data CsSigType pass = CsSig
  { sig_ext :: XCsSig pass
  , sig_body :: LCsType pass
  }

data CsForAllTelescope pass = CsForAll
  { csf_x :: XCsForAll pass
  , csf_bndrs :: [LCsTyVarBndr pass]
  }

type LCsTyVarBndr pass = XRec pass (CsTyVarBndr pass)

data CsTyVarBndr pass
  -- = UserTyVar (XUserTyVar pass) (LIdP pass)
  = KindedTyVar (XKindedTyVar pass) (LIdP pass) (LCsKind pass)
  | ImpKindedTyVar (XImpKindedTyVar pass) (LIdP pass) (LCsKind pass)

data CsType pass
  = CsForAllTy
    { cst_xforall :: XForAllTy pass
    , cst_tele :: CsForAllTelescope pass
    , cst_body :: LCsType pass
    }
  | CsQualTy
    { cst_xqual :: XQualTy pass
    , cst_ctxt :: LCsContext pass -- context of kind variable, not type class, constraints
    , cst_body :: LCsType pass
    }
  | CsTyVar (XTyVar pass) (LIdP pass)
  | CsUnboundTyVar (XUnboundTyVar pass) RdrName
  | CsAppTy (XAppTy pass) (LCsType pass) (LCsType pass)
  | CsFunTy (XFunTy pass) (CsArrow pass) (LCsType pass) (LCsType pass)
  | CsTupleTy (XTupleTy pass) [CsTyTupArg pass]
  | CsSumTy (XSumTy pass) [LCsType pass]
  | CsOpTy (XOpTy pass) (LCsType pass) (LIdP pass) (LCsType pass)
  | CsParTy (XParTy pass) (LCsType pass)
  | CsKindSig (XKdSig pass) (LCsType pass) (LCsKind pass)
    -- function from type to type
  | CsTyLamTy (XTyLamTy pass) (MatchGroup pass (LCsType pass))
  | TySectionL (XTySectionL pass) (LCsType pass) (LCsType pass)
  | TySectionR (XTySectionR pass) (LCsType pass) (LCsType pass)

data CsTyTupArg id
  = TyPresent (XTyPresent id) (LCsType id)
  | TyMissing (XTyMissing id)

data CsArrow pass
  = CsArrow !(XCsArrow pass) !(LCsKind pass)

type family XCsArrow x -- XExplicitMult in ghc

data CsConDetails tyarg arg
  = PrefixCon [tyarg] [arg]
  | InfixCon arg arg
  deriving Data

data CsArg p tm ty
  = CsValArg !(XValArg p) tm
  | CsTypeArg !(XTypeArg p) ty
  | CsArgPar !(XArgPar p)

type family XValArg p
type family XTypeArg p
type family XArgPar p

type LCsTypeArg p = CsArg p (LCsType p) (LCsKind p)
