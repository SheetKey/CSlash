{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module CSlash.Cs.Pat
  ( Pat(..), LPat
  , EpAnnSumPat(..)
  , ConPatTc(..)
  , ConLikeP

  , CsConPatDetails
  , CsConPatTyArg(..)

  , patNeedsParens

  , pprParendLPat
  ) where

import CSlash.Language.Syntax.Pat

import CSlash.Cs.Binds
import CSlash.Cs.Lit
import CSlash.Language.Syntax.Extension
import CSlash.Parser.Annotation
import CSlash.Cs.Extension
import CSlash.Cs.Type
import CSlash.Types.Basic
import CSlash.Types.SrcLoc

import CSlash.Utils.Outputable
import CSlash.Types.Name.Reader (RdrName)
import CSlash.Core.ConLike
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Types.Name (Name)
import Data.Data

type instance XWildPat Ps = NoExtField
type instance XWildPat Rn = NoExtField
type instance XWildPat Tc = Type

type instance XVarPat (CsPass _) = NoExtField
type instance XTyVarPat (CsPass _) = NoExtField

type instance XAsPat Ps = EpToken "@"
type instance XAsPat Rn = NoExtField
type instance XAsPat Tc = NoExtField

type instance XParPat Ps = (EpToken "(", EpToken ")")
type instance XParPat Rn = NoExtField
type instance XParPat Tc = NoExtField

type instance XTuplePat Ps = [AddEpAnn]
type instance XTuplePat Rn = NoExtField
type instance XTuplePat Tc = [Type]

type instance XSumPat Ps = EpAnnSumPat
type instance XSumPat Rn = NoExtField
type instance XSumPat Tc = [Type]

type instance XConPat Ps = [AddEpAnn]
type instance XConPat Rn = NoExtField
type instance XConPat Tc = ConPatTc 

type instance XLitPat (CsPass _) = NoExtField

type instance XNPat Ps = [AddEpAnn]
type instance XNPat Rn = [AddEpAnn]
type instance XNPat Tc = Type

type instance XSigPat Ps = [AddEpAnn]
type instance XSigPat Rn = NoExtField
type instance XSigPat Tc = Type

type instance XKdSigPat Ps = [AddEpAnn]
type instance XKdSigPat Rn = NoExtField
type instance XKdSigPat Tc = Kind

type instance ConLikeP Ps = RdrName
type instance ConLikeP Rn = Name
type instance ConLikeP Tc = ConLike

type instance XConPatTyArg Ps = NoExtField
type instance XConPatTyArg Rn = NoExtField
type instance XConPatTyArg Tc = NoExtField

data EpAnnSumPat = EpAnnSumPat
  { sumPatParens :: [AddEpAnn]
  , sumPatVbarsBefore :: [EpaLocation]
  , sumPatVBarsAfter :: [EpaLocation]
  }
  deriving Data

instance NoAnn EpAnnSumPat where
  noAnn = EpAnnSumPat [] [] []

data ConPatTc = ConPatTc

instance Outputable (CsTyPat p) => Outputable (CsConPatTyArg p) where
  ppr (CsConPatTyArg _ ty) = ppr ty

instance OutputableBndrId p => Outputable (Pat (CsPass p)) where
  ppr = pprPat

pprPatBndr :: OutputableBndr name => name -> SDoc
pprPatBndr var
  = getPprDebug $ \case
  True -> parens (pprBndr LambdaBind var)
  False -> pprPrefixOcc var

pprParendLPat :: (OutputableBndrId p) => PprPrec -> LPat (CsPass p) -> SDoc
pprParendLPat p = pprParendPat p . unLoc

pprParendPat
  :: (OutputableBndrId p)
  => PprPrec -> Pat (CsPass p) -> SDoc
pprParendPat p pat = 
  if patNeedsParens p pat
  then parens (pprPat pat)
  else pprPat pat

patNeedsParens :: IsPass p => PprPrec -> Pat (CsPass p) -> Bool
patNeedsParens p = go
  where
    go :: IsPass q => Pat (CsPass q) -> Bool
    go (WildPat{}) = False
    go (VarPat{}) = False
    go (TuplePat{}) = p >= appPrec
    go (SumPat{}) = False
    go (LitPat _ l) = csLitNeedsParens p l
    go (SigPat{}) = p >= sigPrec

pprPat :: (OutputableBndrId p) => Pat (CsPass p) -> SDoc
pprPat (WildPat{}) = char '_'
pprPat (VarPat _ lvar) = pprPatBndr (unLoc lvar)
pprPat (TuplePat _ pats) = parens (pprWithCommas ppr pats)
pprPat (SumPat _ pat alt arity) = parens (pprAlternative ppr pat alt arity)
pprPat (LitPat _ s) = ppr s
pprPat (SigPat _ pat ty) = ppr pat <+> colon <+> ppr ty

type instance Anno (Pat (CsPass p)) = SrcSpanAnnA
type instance Anno (CsOverLit (CsPass p)) = EpAnnCO
type instance Anno ConLike = SrcSpanAnnN
