module CSlash.Cs.Type where

import CSlash.Language.Syntax.Type
import CSlash.Language.Syntax.Extension
import CSlash.Cs.Extension

instance OutputableBndrId p => Outputable (CsSigType (CsPass p)) where
  ppr (CsSig{ sig_body = body }) = ppr body
