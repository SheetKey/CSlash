module CSlash.Cs.Decls
  (
  ) where

import CSlash.Language.Syntax.Decls

import CSlash.Language.Syntax.Extension
import CSlash.Cs.Extension
import CSlash.Parser.Annotation
import CSlash.Utils.Outputable

instance (OutputableBndrId p) => Outputable (CsDecl (CsPass p)) where
  ppr (ValD _ bind) = ppr bind
  ppr (SigD _ sd) = ppr sd

type instance Anno (CsDecl (CsPass _)) = SrcSpanAnnA
