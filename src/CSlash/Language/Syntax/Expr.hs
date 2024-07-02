module CSlash.Language.Syntax.Expr where

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Basic
import CSlash.Language.Syntax.Lit
import CSlash.Language.Syntax.Pat
import CSlash.Language.Syntax.Type

import CSlash.Types.Fixity
import CSlash.Types.Name.Reader

type LCsExpr p = XRec p (CsExpr p)

data CsExpr p
  = CsVar (XVar p) (LIdP p)
  | CsUnboundVar (XUnboundVar p) RdrName
  | CsLit (XLitE p) (CsLit p)
  | CsLam (XLam p) (MatchGroup p (LCsExpr p))
  | CsApp (XApp p) (LCsExpr p) (LCsExpr p)
  | CsTyLam (XTyLam p) (MatchGroup p (LCsExpr p))
  | CsTyApp (XTyApp p) (LCsExpr p) (LCsExpr p)
  | OpApp (XOpApp p) (LCsExpr p) (LCsExpr p) (LCsExpr p)
  | CsPar (XPar p) (LCsExpr p)
  | SectionL (XSectionL p) (LCsExpr p) (LCsExpr p)
  | SectionR (XSectionR p) (LCsExpr p) (LCsExpr p)
  | ExplicitTuple (XExplicitTuple p) [CsTupArg p]
  | ExplicitSum (XExplicitSum p) ConTag SumWidth (LCsExpr p)
  | CsCase (XCase p) (LCsExpr p) (MatchGroup p (LCsExpr p))
  | CsIf (XIf p) (LCsExpr p) (LCsExpr p) (LCsExpr p)
  | CsMultiIf (XMultiIf p) [LGRHS p (LCsExpr p)]
  | ExprWithTySig (XExprWithTySig p) (LCsExpr p) (LCsType (NoTc p))

data CsTupArg id
  = Present (XPresent id) (LCsExpr id)
  | Missing (XMissing id)

data MatchGroup p body = MG
  { mg_ext :: XMG p body
  , mg_alts :: XRec p [LMatch p body]
  }

type LMatch id body = XRec id (Match id body)

data Match p body = Match
  { m_ext :: XCMatch p body
  , m_ctxt :: CsMatchContext (LIdP (NoTc p))
  , m_pats :: [LPat p]
  , m_grhss :: GRHSs p body
  }

data CsMatchContext fn
  = LamAlt
  | TLamAlt
  | CaseAlt
  | MultiIfAlt

data GRHSs p body
  = GRHSs
    { grhssExt :: XCGRHSs p body
    , grhssGRHSs :: [LGRHS p body]
    }

type LGRHS id body = XRec id (GRHS id body)

data GRHS p body
  = GRHS (XCGRHS p body) [GuardLStmt p] body -- list of GuardLStmt empty for CaseAlt

type LStmt id body = XRec id (StmtLR id id body)

type GuardLStmt id = LStmt id (LCsExpr id)

data StmtLR idL idR body
  = GuardBodyStmt (XGuardBodyStmt idL idR body) body -- GHC BodyStmt
