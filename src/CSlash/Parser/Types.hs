{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

module CSlash.Parser.Types
  ( PatBuilder(..) )
  where

import CSlash.Cs.Extension

import CSlash.Parser.Annotation

import CSlash.Types.Name.Reader

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Type
import CSlash.Language.Syntax.Pat
import CSlash.Language.Syntax.Lit
import CSlash.Types.SrcLoc
import CSlash.Cs.Extension
import CSlash.Cs.Type
import CSlash.Cs.Pat
import CSlash.Cs.Lit
import CSlash.Parser.Annotation
import CSlash.Utils.Outputable
import CSlash.Language.Syntax

data PatBuilder p
  = PatBuilderPat (Pat p)
  | PatBuilderPar (EpToken "(") (LocatedA (PatBuilder p)) (EpToken ")")
  | PatBuilderApp (LocatedA (PatBuilder p)) (LocatedA (PatBuilder p))
  | PatBuilderAppType (LocatedA (PatBuilder p)) (CsTyPat Ps)
  | PatBuilderOpApp (LocatedA (PatBuilder p)) (LocatedN RdrName)
                    (LocatedA (PatBuilder p)) [AddEpAnn]
  | PatBuilderVar (LocatedN RdrName)
  | PatBuilderOverLit (CsOverLit Ps)

-- These instances are here so that they are not orphans
type instance Anno (GRHS Ps (LocatedA (PatBuilder Ps)))             = EpAnnCO
type instance Anno [LocatedA (Match Ps (LocatedA (PatBuilder Ps)))] = SrcSpanAnnL
type instance Anno (Match Ps (LocatedA (PatBuilder Ps)))            = SrcSpanAnnA
type instance Anno (StmtLR Ps Ps (LocatedA (PatBuilder Ps)))     = SrcSpanAnnA

instance Outputable (PatBuilder Ps) where
  ppr (PatBuilderPat p) = ppr p
  ppr (PatBuilderPar _ (L _ p) _) = parens (ppr p)
  ppr (PatBuilderApp (L _ p1) (L _ p2)) = ppr p1 <+> ppr p2
  ppr (PatBuilderAppType (L _ p) t) = ppr p <+> ppr t
  ppr (PatBuilderOpApp (L _ p1) op (L _ p2) _) = ppr p1 <+> ppr op <+> ppr p2
