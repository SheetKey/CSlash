module CSlash.Language.Syntax.Decls where

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Binds

type LCsDecl p = XRec p (CsDecl p)

data CsDecl p
  = ValD (XValD p) (CsBind p)
  | SigD (XSigD p) (Sig p)

data CsGroup p
