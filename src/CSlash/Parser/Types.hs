{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

module CSlash.Parser.Types
  ( SumOrTuple(..)
  , PatBuilder(..) 
  , TyPatBuilder(..)
  ) where

import CSlash.Types.Basic
import CSlash.Types.SrcLoc
import CSlash.Types.Name.Reader
import CSlash.Cs.Extension
import CSlash.Cs.Lit
import CSlash.Cs.Pat
import CSlash.Cs.Type
import CSlash.Utils.Outputable as Outputable
import CSlash.Data.OrdList

import Data.Foldable
import CSlash.Parser.Annotation
import CSlash.Language.Syntax

data SumOrTuple b
  = Sum ConTag Arity (LocatedA b) [EpaLocation] [EpaLocation]
  | Tuple [Either (EpAnn Bool) (LocatedA b)]

data PatBuilder p
  = PatBuilderPat (Pat p)
  | PatBuilderPar (EpToken "(") (LocatedA (PatBuilder p)) (EpToken ")")
  | PatBuilderApp (LocatedA (PatBuilder p)) (LocatedA (PatBuilder p))
  | PatBuilderAppType (LocatedA (PatBuilder p)) (CsTyPat Ps) [AddEpAnn]
  | PatBuilderOpApp (LocatedA (PatBuilder p)) (LocatedN RdrName)
                    (LocatedA (PatBuilder p)) [AddEpAnn]
  | PatBuilderConOpApp (LocatedA (PatBuilder p)) (LocatedN RdrName)
                       (LocatedA (PatBuilder p)) [AddEpAnn]
  | PatBuilderVar (LocatedN RdrName)
  | PatBuilderCon (LocatedN RdrName)
  | PatBuilderOverLit (CsOverLit Ps)
  | PatBuilderArgList [LocatedA (PatBuilder p)]

-- These instances are here so that they are not orphans
type instance Anno (GRHS Ps (LocatedA (PatBuilder Ps)))             = EpAnnCO
type instance Anno [LocatedA (Match Ps (LocatedA (PatBuilder Ps)))] = SrcSpanAnnL
type instance Anno (Match Ps (LocatedA (PatBuilder Ps)))            = SrcSpanAnnA
type instance Anno (StmtLR Ps Ps (LocatedA (PatBuilder Ps)))     = SrcSpanAnnA

instance Outputable (PatBuilder Ps) where
  ppr (PatBuilderPat p) = ppr p
  ppr (PatBuilderPar _ (L _ p) _) = parens (ppr p)
  ppr (PatBuilderApp (L _ p1) (L _ p2)) = ppr p1 <+> ppr p2
  ppr (PatBuilderAppType (L _ p) t _) = ppr p <+> braces (ppr t)
  ppr (PatBuilderOpApp (L _ p1) op (L _ p2) _) = ppr p1 <+> ppr op <+> ppr p2
  ppr (PatBuilderConOpApp (L _ p1) op (L _ p2) _) = ppr p1 <+> ppr op <+> ppr p2
  ppr (PatBuilderVar v) = ppr v
  ppr (PatBuilderCon c) = ppr c
  ppr (PatBuilderOverLit l) = ppr l
  ppr (PatBuilderArgList l) = hsep $ ppr <$> l

data TyPatBuilder p
  = TyPatBuilderPat (Pat p)
  | TyPatBuilderPar (EpToken "(") (LocatedA (TyPatBuilder p)) (EpToken ")")
  | TyPatBuilderApp (LocatedA (TyPatBuilder p)) (LocatedA (TyPatBuilder p))
  | TyPatBuilderOpApp (LocatedA (TyPatBuilder p)) (LocatedN RdrName)
                      (LocatedA (TyPatBuilder p)) [AddEpAnn]
  | TyPatBuilderConOpApp (LocatedA (TyPatBuilder p)) (LocatedN RdrName)
                         (LocatedA (TyPatBuilder p)) [AddEpAnn]
  | TyPatBuilderVar (LocatedN RdrName)
  | TyPatBuilderCon (LocatedN RdrName)
  | TyPatBuilderArgList [LocatedA (TyPatBuilder p)]

type instance Anno (GRHS Ps (LocatedA (TyPatBuilder Ps)))             = EpAnnCO
type instance Anno [LocatedA (Match Ps (LocatedA (TyPatBuilder Ps)))] = SrcSpanAnnL
type instance Anno (Match Ps (LocatedA (TyPatBuilder Ps)))            = SrcSpanAnnA
type instance Anno (StmtLR Ps Ps (LocatedA (TyPatBuilder Ps)))     = SrcSpanAnnA

instance Outputable (TyPatBuilder Ps) where
  ppr (TyPatBuilderPat p) = ppr p
  ppr (TyPatBuilderPar _ (L _ p) _) = parens (ppr p)
  ppr (TyPatBuilderApp (L _ p1) (L _ p2)) = ppr p1 <+> ppr p2
  ppr (TyPatBuilderOpApp (L _ p1) op (L _ p2) _) = ppr p1 <+> ppr op <+> ppr p2
  ppr (TyPatBuilderConOpApp (L _ p1) op (L _ p2) _) = ppr p1 <+> ppr op <+> ppr p2
  ppr (TyPatBuilderVar v) = ppr v
  ppr (TyPatBuilderCon c) = ppr c
  ppr (TyPatBuilderArgList l) = hsep $ ppr <$> l
