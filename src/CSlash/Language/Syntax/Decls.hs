module CSlash.Language.Syntax.Decls where

type LCsDecl p = XRec p (CsDecl p)

data CsDecl p
  = ValD (XValD p) (CsBind p)
  | SigD (XSigD p) (Sig p)
