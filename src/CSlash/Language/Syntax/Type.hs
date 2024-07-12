{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module CSlash.Language.Syntax.Type where

import {-# SOURCE #-} CSlash.Language.Syntax.Expr

import CSlash.Language.Syntax.Extension

import CSlash.Language.Syntax.Kind

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

data CsSigType pass = CsSig
  { sig_ext :: XCsSig pass
  , sig_body :: LCsType pass
  }

data CsForAllTelescope pass = CsForAllInvis
  { csf_xinvis :: XCsForAllInvis pass
  , csf_invis_bndrs :: [LCsTyVarBndr pass]
  }

type LCsTyVarBndr pass = XRec pass (CsTyVarBndr pass)

data CsTyVarBndr pass
  -- = UserTyVar (XUserTyVar pass) (LIdP pass)
  = KindedTyVar (XKindedTyVar pass) (LIdP pass) (LCsKind pass)

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
  | CsAppTy (XAppTy pass) (LCsType pass) (LCsType pass)
  | CsFunTy (XFunTy pass) (CsArrow pass) (LCsType pass) (LCsType pass)
  | CsTupleTy (XTupleTy pass) [LCsType pass]
  | CsSumTy (XSumTy pass) [LCsType pass]
  | CsParTy (XParTy pass) (LCsType pass)
  | CsKindSig (XKdSig pass) (LCsType pass) (LCsKind pass)
    -- function from type to type
  | CsTyLamTy (XTyLamTy pass) (MatchGroup pass (LCsType pass))
  --    -- type applied to a type
  --  | CsTyAppTy (XTyAppTy pass) (LCsType pass) (LCsType pass)

data CsArrow pass
  = CsArrow !(XCsArrow pass) !(LCsKind pass)

type family XCsArrow x -- XExplicitMult in ghc

data CsArg p tm ty
  = CsValArg !(XValArg p) tm
  | CsTypeArg !(XTypeArg p) ty
  | CsArgPar !(XArgPar p)

type family XValArg p
type family XTypeArg p
type family XArgPar p

type LCsTypeArg p = CsArg p (LCsType p) (LCsKind p)
