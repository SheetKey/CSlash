{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
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
  , EpAnnImpPat(..)
  , ConPatTc(..)
  , ConLikeP
  , CsPatExpansion(..)
  , XXPatCsTc(..)

  , CsConPatDetails, csConPatArgs, csConPatTyArgs
  , CsConPatTyArg(..)

  , patNeedsParens

  , pprParendLPat
  ) where

import Prelude hiding ((<>))

import CSlash.Language.Syntax.Pat

import CSlash.Cs.Binds
import CSlash.Cs.Lit
import CSlash.Language.Syntax.Extension
import CSlash.Parser.Annotation
import CSlash.Cs.Extension
import CSlash.Cs.Type
import CSlash.Cs.Kind
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
type instance XWildPat Tc = Type (TyVar KiVar) KiVar

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
type instance XTuplePat Tc = [Type (TyVar KiVar) KiVar]

type instance XSumPat Ps = EpAnnSumPat
type instance XSumPat Rn = NoExtField
type instance XSumPat Tc = [Type (TyVar KiVar) KiVar]

type instance XConPat Ps = [AddEpAnn]
type instance XConPat Rn = NoExtField
type instance XConPat Tc = ConPatTc 

type instance XLitPat (CsPass _) = NoExtField

type instance XNPat Ps = [AddEpAnn]
type instance XNPat Rn = [AddEpAnn]
type instance XNPat Tc = Type (TyVar KiVar) KiVar

type instance XSigPat Ps = [AddEpAnn]
type instance XSigPat Rn = NoExtField
type instance XSigPat Tc = Type (TyVar KiVar) KiVar

type instance XKdSigPat Ps = [AddEpAnn]
type instance XKdSigPat Rn = NoExtField
type instance XKdSigPat Tc = Kind KiVar

type instance XImpPat Ps = EpAnnImpPat
type instance XImpPat Rn = NoExtField
type instance XImpPat Tc = NoExtField

type instance XXPat Ps = DataConCantHappen
type instance XXPat Rn = CsPatExpansion (Pat Rn) (Pat Rn)
type instance XXPat Tc = XXPatCsTc

type instance ConLikeP Ps = RdrName
type instance ConLikeP Rn = Name
type instance ConLikeP Tc = ConLike (TyVar KiVar) KiVar

type instance XConPatTyArg Ps = [AddEpAnn]
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

data EpAnnImpPat = EpAnnImpPat
  { impPatOCurly :: EpToken "{"
  , impPatCCurly :: EpToken "}"
  }
  deriving Data  

-- ---------------------------------------------------------------------

data XXPatCsTc = ExpansionPat (Pat Rn) (Pat Tc)

data CsPatExpansion a b = CsPatExpanded a b
  deriving Data

-- ---------------------------------------------------------------------

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

patNeedsParens :: forall p. IsPass p => PprPrec -> Pat (CsPass p) -> Bool
patNeedsParens p = go @p
  where
    go :: forall q. IsPass q => Pat (CsPass q) -> Bool
    go (WildPat{}) = False
    go (VarPat{}) = False
    go (TyVarPat{}) = True
    go (AsPat{}) = False
    go (ParPat{}) = False
    go (TuplePat{}) = p >= appPrec
    go (SumPat{}) = False
    go (ConPat { pat_args = ds }) = conPatNeedsParens p ds
    go (LitPat _ l) = csLitNeedsParens p l
    go (NPat _ lol _ _) = csOverLitNeedsParens p (unLoc lol)
    go (SigPat{}) = p >= sigPrec
    go (KdSigPat{}) = p >= sigPrec
    go (ImpPat{}) = False
    go (XPat ext) = case csPass @q of
      Rn -> case ext of
        CsPatExpanded _ pat -> go pat
      Tc -> case ext of
        ExpansionPat _ pat -> go pat

conPatNeedsParens :: PprPrec -> CsConDetails t a -> Bool
conPatNeedsParens p = go
  where 
    go (PrefixCon ts args) = p >= appPrec && (not (null args) || not (null ts))
    go (InfixCon {}) = p >= opPrec

pprPat :: forall p. (OutputableBndrId p) => Pat (CsPass p) -> SDoc
pprPat (WildPat{}) = char '_'
pprPat (VarPat _ lvar) = pprPatBndr (unLoc lvar)
pprPat (TyVarPat _ lvar) = pprPatBndr (unLoc lvar)
pprPat (AsPat _ name pat) = hcat [pprPrefixOcc (unLoc name), char '@', pprParendLPat appPrec pat]
pprPat (ParPat _ pat) = parens (ppr pat)
pprPat (TuplePat _ pats) = parens (pprWithCommas ppr pats)
pprPat (SumPat _ pat alt arity) = parens (pprAlternative ppr pat alt arity)
pprPat (ConPat { pat_con = con, pat_args = details, pat_con_ext = ext }) =
  case csPass @p of
    Ps -> pprUserCon (unLoc con) details
    Rn -> pprUserCon (unLoc con) details
    Tc -> sdocOption sdocPrintTypecheckerElaboration $ \case
      False -> pprUserCon (unLoc con) details
      True -> error "pprPat"
pprPat (LitPat _ s) = ppr s
pprPat (NPat _ l Nothing _) = ppr l
pprPat (NPat _ l (Just _) _) = char '-' <> ppr l
pprPat (SigPat _ pat ty) = ppr pat <+> colon <+> ppr ty
pprPat (KdSigPat _ pat kd) = ppr pat <+> colon <+> ppr kd
pprPat (ImpPat _ pat) = braces $ ppr pat
pprPat (XPat ext) = case csPass @p of
  Rn -> case ext of
    CsPatExpanded orig _ -> pprPat orig
  Tc -> case ext of
    ExpansionPat orig _ -> pprPat orig

pprUserCon
  :: (OutputableBndr con, OutputableBndrId p, Outputable (Anno (IdCsP p)))
  => con -> CsConPatDetails (CsPass p) -> SDoc
pprUserCon c (InfixCon p1 p2) = ppr p1 <+> pprInfixOcc c <+> ppr p2
pprUserCon c details = pprPrefixOcc c <+> pprConArgs details

pprConArgs
  :: (OutputableBndrId p, Outputable (Anno (IdCsP p)))
  => CsConPatDetails (CsPass p) -> SDoc
pprConArgs (PrefixCon ts pats) = fsep (pprTyArgs ts : map (pprParendLPat appPrec) pats)
  where pprTyArgs tyargs = fsep (map ppr tyargs)
pprConArgs (InfixCon p1 p2) = sep [ pprParendLPat appPrec p1, pprParendLPat appPrec p2 ]

type instance Anno (Pat (CsPass p)) = SrcSpanAnnA
type instance Anno (CsOverLit (CsPass p)) = EpAnnCO
type instance Anno (ConLike tv kv) = SrcSpanAnnN
