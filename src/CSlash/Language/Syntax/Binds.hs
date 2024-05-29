module CSlash.Language.Syntax.Binds where

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Expr
import CSlash.Language.Syntax.Type
import CSlash.Language.Syntax.Kind

import CSlash.Types.Fixity

type CsBind id = CsBindLR id id

data CsBindLR idL idR
  = FunBind
    { fun_ext :: XFunBind idL idR
    , fun_id :: LIdP idL
    , fun_matches :: MatchGroup idR (LCsExpr idR)
    }
  | TySynBind
    { tysyn_ext :: XTySynBind idL idR
    , tysyn_id :: LIdP idL
    , tysyn_rhs :: LCsType idR
    }
  | VarBind
    { var_ext :: XVarBind idL idR
    , var_id :: IdP idL
    , var_rhs :: LCsExpr idR
    }

data Sig pass
  = TypeSig (XTypeSig pass) (LIdP pass) (LCsType pass)
  | KindSig (XKindSig pass) (LIdP pass) (LCsKind pass)
  | FixSig (XFixSig pass) (FixitySig pass)

data FixitySig pass
  = FixitySig (XFixitySig pass) (LIdP pass) Fixity
