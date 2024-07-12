module CSlash.Language.Syntax.Binds where

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Expr
import CSlash.Language.Syntax.Type
import CSlash.Language.Syntax.Kind

import CSlash.Types.Fixity

type LCsBind id = XRec id (CsBindLR id id)

type CsBind id = CsBindLR id id

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

data LCsSig p = XRec p (Sig p)

data Sig pass
  = TypeSig (XTypeSig pass) (LIdP pass) (LCsType pass)
  | KindSig (XKindSig pass) (LIdP pass) (LCsKind pass)
  | FixSig (XFixSig pass) (FixitySig pass)

data FixitySig pass
  = FixitySig (XFixitySig pass) (LIdP pass) Fixity
