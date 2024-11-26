{-# LANGUAGE TypeFamilies #-}

module CSlash.Language.Syntax.Expr where

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Basic
import CSlash.Language.Syntax.Lit
import CSlash.Language.Syntax.Pat
import CSlash.Language.Syntax.Type
import CSlash.Language.Syntax.Binds

import CSlash.Types.Fixity
import CSlash.Types.Name.Reader

type LCsExpr p = XRec p (CsExpr p)

type family SyntaxExpr p

data CsExpr p
  = CsVar (XVar p) (LIdP p)
  | CsUnboundVar (XUnboundVar p) RdrName
  | CsOverLit (XOverLitE p) (CsOverLit p)
  | CsLit (XLitE p) (CsLit p)
  | CsLam (XLam p) (MatchGroup p (LCsExpr p))
  | CsApp (XApp p) (LCsExpr p) (LCsExpr p)
  | CsTyLam (XTyLam p) (MatchGroup p (LCsExpr p)) -- could probably remove (add Matchcontext to cslam fields)
  | CsTyApp (XTyApp p) (LCsExpr p) (LCsExpr p) -- remove
  | OpApp (XOpApp p) (LCsExpr p) (LCsExpr p) (LCsExpr p)
  -- this could change to BinOp:
  -- we can parse prefix occurence as a binary operator (maybe a bad idea)
  | NegApp (XNegApp p) (LCsExpr p) (SyntaxExpr p)
  | CsPar (XPar p) (LCsExpr p)
  | SectionL (XSectionL p) (LCsExpr p) (LCsExpr p)
  | SectionR (XSectionR p) (LCsExpr p) (LCsExpr p)
  | ExplicitTuple (XExplicitTuple p) [CsTupArg p]
  | ExplicitSum (XExplicitSum p) ConTag SumWidth (LCsExpr p)
  | CsCase (XCase p) (LCsExpr p) (MatchGroup p (LCsExpr p))
  | CsIf (XIf p) (LCsExpr p) (LCsExpr p) (LCsExpr p)
  | CsMultiIf (XMultiIf p) [LGRHS p (LCsExpr p)]
  | CsLet (XLet p) (CsLocalBinds p) (LCsExpr p)
  | ExprWithTySig (XExprWithTySig p) (LCsExpr p) (LCsSigType (NoTc p))
  | CsEmbTy (XEmbTy p) (LCsType (NoTc p)) -- for cstylam and cstyapp

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
  , m_pats :: XRec p [LPat p]
  , m_grhss :: GRHSs p body
  }

data CsMatchContext fn
  = LamAlt
  | TyLamAlt -- for biglam (term level lambda that binds a type)
  | CaseAlt
  | MultiIfAlt
  | TyLamTyAlt -- for type level lambdas

data CsStmtContext fn
  = PatGuard (CsMatchContext fn)

data GRHSs p body
  = GRHSs
    { grhssExt :: XCGRHSs p body
    , grhssGRHSs :: [LGRHS p body]
    }

type LGRHS id body = XRec id (GRHS id body)

data GRHS p body
  = GRHS (XCGRHS p body) [GuardLStmt p] body

type LStmt id body = XRec id (StmtLR id id body)

type GuardLStmt id = LStmt id (LCsExpr id)

data StmtLR idL idR body
  = BindStmt (XBindStmt idL idR body) (LPat idL) body -- used in pattern guards
  | BodyStmt (XBodyStmt idL idR body) body
  | LetStmt (XLetStmt idL idR body) (CsLocalBindsLR idL idR)

isPatSynCtxt :: CsMatchContext fn -> Bool
isPatSynCtxt ctxt = case ctxt of
  _ -> False
