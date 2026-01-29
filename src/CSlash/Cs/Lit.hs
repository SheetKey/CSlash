{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module CSlash.Cs.Lit
  ( module CSlash.Language.Syntax.Lit
  , module CSlash.Cs.Lit
  ) where

import CSlash.Types.Basic
import CSlash.Types.SourceText
import CSlash.Core.Type
import CSlash.Utils.Outputable
import CSlash.Cs.Extension
import CSlash.Language.Syntax.Expr (CsExpr)
import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Lit

import CSlash.Utils.Panic

type instance XCsChar (CsPass _) = SourceText
type instance XCsString (CsPass _) = SourceText
type instance XCsInt (CsPass _) = NoExtField
type instance XCsDouble (CsPass _) = NoExtField

data OverLitRn = OverLitRn
  { ol_from_fun :: LIdP Rn
  }

data OverLitTc = OverLitTc
  { ol_witness :: CsExpr Tc
  , ol_type :: Type Tc
  }

type instance XOverLit Ps = NoExtField
type instance XOverLit Rn = OverLitRn
type instance XOverLit Tc = OverLitTc
type instance XOverLit Zk = OverLitTc

csOverLitNeedsParens :: PprPrec -> CsOverLit x -> Bool
csOverLitNeedsParens p (OverLit { ol_val = olv }) = go olv
  where
    go :: OverLitVal -> Bool
    go (CsIntegral x) = p > topPrec && il_neg x
    go (CsFractional x) = p > topPrec && fl_neg x
    go (CsIsString {}) = False

csLitNeedsParens :: PprPrec -> CsLit x -> Bool
csLitNeedsParens p = go
  where
    go (CsChar{}) = False
    go (CsString{}) = False
    go (CsInt _ x) = p > topPrec && il_neg x
    go (CsDouble{}) = False

convertLit :: CsLit (CsPass p1) -> CsLit (CsPass p2)
convertLit (CsChar a x) = CsChar a x
convertLit _ = panic "convertLit"

instance Outputable (CsLit (CsPass p)) where
  ppr (CsChar st c) = pprWithSourceText st (pprCsChar c)
  ppr (CsString st s) = pprWithSourceText st (pprCsString s)
  ppr (CsInt _ i) = pprWithSourceText (il_text i) (integer (il_value i))
  ppr (CsDouble _ d) = ppr d

instance OutputableBndrId p => Outputable (CsOverLit (CsPass p)) where
  ppr = undefined
