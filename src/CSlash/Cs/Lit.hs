module CSlash.Cs.Lit where

import CSlash.Syntax.Language.Lit

import CSlash.Types.Basic

csLitNeedsParens :: PprPrec -> CsLit x -> Bool
csLitNeedsParens p = go
  where
    go (CsChar{}) = False
    go (CsString{}) = False
    go (CsInt _ x) = p > topPrec && il_neg x
    go (CsDouble{}) = False
