{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module CSlash.Cs.Lit where

import CSlash.Language.Syntax.Lit
import CSlash.Language.Syntax.Extension
import CSlash.Cs.Extension
import CSlash.Types.SourceText
import CSlash.Types.Basic
import CSlash.Utils.Outputable

type instance XCsChar (CsPass _) = SourceText
type instance XCsString (CsPass _) = SourceText

csLitNeedsParens :: PprPrec -> CsLit x -> Bool
csLitNeedsParens p = go
  where
    go (CsChar{}) = False
    go (CsString{}) = False
    go (CsInt _ x) = p > topPrec && il_neg x
    go (CsDouble{}) = False

instance Outputable (CsLit (CsPass p)) where
  ppr (CsChar st c) = pprWithSourceText st (pprCsChar c)
  ppr (CsString st s) = pprWithSourceText st (pprCsString s)
  ppr (CsInt _ i) = pprWithSourceText (il_text i) (integer (il_value i))
  ppr (CsDouble _ d) = ppr d
