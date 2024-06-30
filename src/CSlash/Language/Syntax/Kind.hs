module CSlash.Language.Syntax.Kind where

import CSlash.Language.Syntax.Extension

type LCsKind pass = XRec pass (CsKind pass)

data CsKind pass
  = CsUKd (XUKd pass)
  | CsAKd (XAKd pass)
  | CsLKd (XLKd pass)
  | CsKdVar (XKdVar pass) (LIdP pass)
  | CsFunKd (XFunKd pass) (LCsKind pass) (LCsKind pass)
  | CsQualKd
    { csk_xqual :: XQualKd pass
    , csk_ctxt :: LCsContext pass
    , csk_body :: LCsKind pass
    }
  | CsParKd (XParKd pass) (LCsKind pass)

type LCsContext pass = XRec pass (CsContext pass)

type CsContext pass = [LCsKdRel pass]

type LCsKdRel pass = XRec pass (CsKdRel pass)

data CsKdRel pass
  = CsKdLT (XKdLT pass) (LCsKind pass) (LCsKind pass)
  | CsKdLTEQ (XKdLTEQ pass) (LCsKind pass) (LCsKind pass)
