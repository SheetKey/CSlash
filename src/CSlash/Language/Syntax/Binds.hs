module CSlash.Language.Syntax.Binds where

import {-# SOURCE #-} CSlash.Language.Syntax.Expr
  ( LCsExpr, MatchGroup, GRHSs )

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Type
import CSlash.Language.Syntax.Kind

import CSlash.Types.Fixity
import CSlash.Data.Bag (Bag)

type CsLocalBinds id = CsLocalBindsLR id id

type LCsLocalBinds id = XRec id (CsLocalBinds id)

data CsLocalBindsLR idL idR
  = CsValBinds (XCsValBinds idL idR)
               (CsValBindsLR idL idR)
  | EmptyLocalBinds (XEmptyLocalBinds idL idR)

data CsValBindsLR idL idR
  = ValBinds (XValBinds idL idR)
             (LCsBindsLR idL idR) [LSig idR]

-- ---------------------------------------------------------------------

type LCsBind id = XRec id (CsBindLR id id)

type CsBind id = CsBindLR id id

type LCsBindsLR idL idR = Bag (LCsBindLR idL idR)

type LCsBindLR idL idR = XRec idL (CsBindLR idL idR)

data CsBindLR idL idR
  = FunBind -- for all top level binds, not just functions
    { fun_ext :: XFunBind idL idR
    , fun_id :: LIdP idL
    , fun_body :: (LCsExpr idR)
    }
  | TyFunBind -- for all type synonyms, not just type functions
    { tyfun_ext :: XTyFunBind idL idR
    , tyfun_id :: LIdP idL
    , tyfun_body :: LCsType idR
    }
  | TCVarBind -- only introduced by typechecker
    { tcvar_ext :: XTCVarBind idL idR
    , tcvar_id :: IdP idL
    , tcvar_rhs :: LCsExpr idR
    }

data LSig p = XRec p (Sig p)

data Sig pass
  = TypeSig (XTypeSig pass) (LIdP pass) (LCsType pass)
  | KindSig (XKindSig pass) (LIdP pass) (LCsKind pass)
  | FixSig (XFixSig pass) (FixitySig pass)

data FixitySig pass
  = FixitySig (XFixitySig pass) (LIdP pass) Fixity
