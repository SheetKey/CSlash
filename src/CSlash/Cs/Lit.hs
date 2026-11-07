{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}

module CSlash.Cs.Lit
  ( module CSlash.Language.Syntax.Lit
  , module CSlash.Cs.Lit
  ) where

import Prelude hiding ((<>))

import {-# SOURCE #-} CSlash.Cs.Expr (pprExpr)

import CSlash.Types.Basic
import CSlash.Types.Name
import CSlash.Types.SourceText
import CSlash.Types.Var.KiVar
import {-# SOURCE #-} CSlash.Core.Rep (Type, KiCon)
import CSlash.Utils.Outputable
import CSlash.Cs.Extension
import CSlash.Language.Syntax.Expr (CsExpr)
import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Lit

import CSlash.Builtin.Types.Prim (fromIntegerKiCon)

import CSlash.Utils.Panic

type instance XCsChar (CsPass _) = SourceText
type instance XCsString (CsPass _) = SourceText
type instance XCsInt (CsPass _) = NoExtField
type instance XCsDouble (CsPass _) = NoExtField

data OverLitP p = OverLitP
  { ol_proj :: Name
  , ol_type :: Type p
  }

type instance XOverLit Ps = NoExtField
type instance XOverLit Rn = NoExtField
type instance XOverLit Tc = OverLitP Tc
type instance XOverLit Zk = OverLitP Zk

pprXOverLit :: OutputableBndrId p => CsPass p -> XOverLit (CsPass p) -> SDoc
pprXOverLit Ps noExt = ppr noExt
pprXOverLit Rn noExt = ppr noExt
pprXOverLit Tc (OverLitP n t) = ppr t <> dot <> ppr n
pprXOverLit Zk (OverLitP n t) = ppr t <> dot <> ppr n

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

overLitFromKiCon :: OverLitVal -> ([KiVar Zk], KiCon Zk, Name)
overLitFromKiCon CsIntegral{} = fromIntegerKiCon
overLitFromKiCon CsFractional{} = panic "CsFractional kicon"
overLitFromKiCon CsIsString{} = panic "CsIsString kicon"

instance Outputable (CsLit (CsPass p)) where
  ppr (CsChar st c) = pprWithSourceText st (pprCsChar c)
  ppr (CsString st s) = pprWithSourceText st (pprCsString s)
  ppr (CsInt _ i) = pprWithSourceText (il_text i) (integer (il_value i))
  ppr (CsDouble _ d) = ppr d

instance OutputableBndrId p => Outputable (CsOverLit (CsPass p)) where
  ppr (OverLit ext val) = ppr val <+> (whenPprDebug (parens (pprXOverLit (csPass @p) ext)))

instance Outputable OverLitVal where
  ppr (CsIntegral i) = pprWithSourceText (il_text i) (integer (il_value i))
  ppr (CsFractional f) = ppr f
  ppr (CsIsString st s) = pprWithSourceText st (pprCsString s)
