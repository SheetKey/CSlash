module CSlash.Cs.Pat where

import CSlash.Language.Syntax.Extension
import CSlash.Cs.Extension
import CSlash.Types.Basic
import CSlash.Utils.Outputable

pprParendLPat :: (OutputableBndrId p) => PprPrec -> LPat (CsPass p) -> SDoc
pprParendLPat p = pprParendPat p . unloc
