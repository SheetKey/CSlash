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

type CsValBinds id = CsValBindsLR id id

data CsValBindsLR idL idR
  = ValBinds (XValBinds idL idR)
             (LCsBindsLR idL idR) [LSig idR]
  | XValBindsLR !(XXValBindsLR idL idR)

-- ---------------------------------------------------------------------

type LCsBind id = LCsBindLR id id

type LCsBinds id = LCsBindsLR id id

type CsBind id = CsBindLR id id

type LCsBindsLR idL idR = [LCsBindLR idL idR]

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
    , tyfun_mrecord :: Maybe (LCsRecord idR)
    }
  | TCVarBind -- only introduced by typechecker
    { tcvar_ext :: XTCVarBind idL idR
    , tcvar_id :: IdP idL
    , tcvar_rhs :: LCsExpr idR
    }
  | XCsBindsLR !(XXCsBindsLR idL idR)

type LSig p = XRec p (Sig p)

data Sig pass
  = TypeSig (XTypeSig pass) (LIdP pass) (LCsSigType pass)
  | KindSig (XKindSig pass) (LIdP pass) (LCsKind pass)
  | FixSig (XFixSig pass) (FixitySig pass)

type LFixitySig pass = XRec pass (FixitySig pass)

data FixitySig pass
  = FixitySig (XFixitySig pass) (LIdP pass) Fixity

{- Record decls

Renaming story:
Records can occur in the following places:
1. type syn decls (tyfun_mrecord :: Maybe (LCsRecord idR)): type List = ... .{ records }
2. top level named record decls: record Name = .{ records }
3. On universally quantified type variables: forall a.{ records }

During parsing, if (3) is encountered, we add an anonymous records to the top level named record
state (where (2) lives). This ensures that during renaming, LOCAL record names are in scope.
Anonymous records are attatched with local information to allow for disambiguation.

Record namespaces are fixed during parsing:
1. mkTyFunBind

Records can contain fixity info. This is added to 'cs_fixds' in 'mkGroup'.
-}

type LCsRecord p = XRec p (CsRecord p)
data CsRecord pass = CsRecord (XCsRecord pass) [LSig pass] -- ONLY Type Sigs
-- TODO: We don't really want to use 'LSig':
-- We don't actually need a RdrName, OccName is semantically correct (as of now rows can unly be unqual RdrNames, which are just OccNames.)
