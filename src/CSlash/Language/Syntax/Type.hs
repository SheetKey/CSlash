module CSlash.Language.Syntax.Type where

import CSlash.Language.Syntax.Extension

import CSlash.Language.Syntax.Kind

type LCsType pass = XRec pass (CsType pass)

data CsPatSigType pass = CsPS
  { csps_ext :: XCsPS pass
  , csps_body :: LCsType pass
  }

data CsForAllTelescope pass = CsForAllInvis
  { csf_xinvis :: XCsForAllInvis pass
  , csf_invis_bndr :: LCsTyVarBndr pass
  }

type LCsTyVarBndr pass = XRec pass (CsTyVarBndr pass)

data CsTyVarBndr
  -- = UserTyVar (XUserTyVar pass) (LIdP pass)
  = KindedTyVar (XKindedTyVar pass) (LIdP pass) (LCsKind pass)

data CsType pass
  = CsForAllTy
    { cst_xforall :: XForAllTy pass
    , cst_tele :: CsForAllTelescope pass
    , cst_body :: LCsType pass
    }
  | CsTyVar (XTyVar pass) (LIdP pass)
  | CsAppTy (XAppTy pass) (LCsType pass) (LCsType pass)
  | CsFunTy (XFunTy pass) (CsArrow pass) (LCsType pass) (LCsType pass)
  | CsTupleTy (XTupleTy pass) [LCsType pass]
  | CsSumTy (XSumTy pass) [LCsType pass]
  | CsParTy (XParTy pass) (LCsType pass)
  | CsKindSig (XKdSig pass) (LCsType pass) (LCsKind pass)

data CsArrow pass
  = CsArrow !(XCsArrow pass) !(LCsKind pass)

type family XCsArrow x
