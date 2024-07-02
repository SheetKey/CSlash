module CSlash.Language.Syntax.Decls where

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Binds

type LCsDecl p = XRec p (CsDecl p)

data CsDecl p
  = ValD (XValD p) (CsBind p) -- top level function or type function
  | SigD (XSigD p) (Sig p) -- top level type of kind sig for a ValD
