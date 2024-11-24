{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module CSlash.Cs.Type
  ( CsArrow(..)
  , pprCsArrow
  
  , CsType(..), LCsType
  , CsForAllTelescope(..), CsTyVarBndr(..), LCsTyVarBndr
  , CsPatSigType(..)
  , CsTyPat(..)
  , CsSigType(..), LCsSigType
  , CsTyTupArg(..)

  , CsConDetails(..)

  , module CSlash.Cs.Type
  ) where

import Prelude hiding ((<>))

import CSlash.Types.Fixity (LexicalFixity(..))
import CSlash.Language.Syntax.Type
import {-# SOURCE #-} CSlash.Language.Syntax.Expr
import CSlash.Language.Syntax.Extension
import CSlash.Cs.Extension
import CSlash.Cs.Kind
import CSlash.Types.Basic
import CSlash.Types.SrcLoc
import CSlash.Types.Name
import CSlash.Types.Name.Reader
import CSlash.Parser.Annotation
import CSlash.Utils.Outputable
import CSlash.Core.Ppr (pprOcc)
import CSlash.Builtin.Names ( negateName )

import Data.Data hiding (Fixity(..))

type instance XCsForAll (CsPass _) = EpAnnForallTy

type EpAnnForallTy = EpAnn (AddEpAnn, AddEpAnn)

mkCsForAllTele :: EpAnnForallTy -> [LCsTyVarBndr (CsPass p)] -> CsForAllTelescope (CsPass p)
mkCsForAllTele an bndrs = CsForAll { csf_x = an, csf_bndrs = bndrs }

type instance XCsPS Ps = EpAnnCO
type instance XCsPS Rn = CsPSRn
type instance XCsPS Tc = CsPSRn

type instance XCsTP Ps = NoExtField
type instance XCsTP Rn = CsTyPatRn
type instance XCsTP Tc = DataConCantHappen

data CsPSRn = CsPSRn
  { csps_imp_kvs :: [Name]
  }
  deriving Data

data CsTyPatRn = CsTPRn
  { cstp_nwcs :: [Name]
  , cstp_imp_tvs :: [Name]
  , cstp_exp_tvs :: [Name]
  }
  deriving Data

type instance XCsSig Ps = NoExtField
type instance XCsSig Rn = [Name]
type instance XCsSig Tc = [Name]

type instance XKindedTyVar (CsPass _) = [AddEpAnn]
type instance XImpKindedTyVar (CsPass _) = [AddEpAnn]

mkCsPatSigType :: EpAnnCO -> LCsType Ps -> CsPatSigType Ps
mkCsPatSigType ann x = CsPS { csps_ext = ann
                            , csps_body = x }

mkCsTyPat :: LCsType Ps -> CsTyPat Ps
mkCsTyPat x = CsTP { cstp_ext = noExtField
                   , cstp_body = x }

type instance XForAllTy (CsPass _) = NoExtField
type instance XQualTy (CsPass _) = NoExtField
type instance XTyVar (CsPass _) = [AddEpAnn]
type instance XUnboundTyVar Ps = Maybe EpAnnUnboundTyVar
type instance XUnboundTyVar Rn = NoExtField
type instance XUnboundTyVar Tc = DataConCantHappen
type instance XAppTy (CsPass _) = NoExtField
type instance XFunTy (CsPass _) = NoExtField
type instance XTupleTy (CsPass _) = AnnParen
type instance XSumTy (CsPass _) = AnnParen
type instance XOpTy (CsPass _) = [AddEpAnn]
type instance XParTy (CsPass _) = (EpToken "(", EpToken ")")
type instance XKdSig (CsPass _) = [AddEpAnn]
type instance XTyLamTy (CsPass _) = [AddEpAnn]

type instance XTySectionL Ps = NoExtField
type instance XTySectionR Ps = NoExtField
type instance XTySectionL Rn = NoExtField
type instance XTySectionR Rn = NoExtField
type instance XTySectionL Tc = DataConCantHappen
type instance XTySectionR Tc = DataConCantHappen

type instance XTyPresent (CsPass _) = NoExtField

type instance XTyMissing Ps = EpAnn Bool
type instance XTyMissing Rn = NoExtField
type instance XTyMissing Tc = NoExtField -- should be Scaled Type

data EpAnnUnboundTyVar = EpAnnUnboundTyVar
  { csUnboundTyBackquotes :: (EpaLocation, EpaLocation)
  , csUnboundTyHole :: EpaLocation
  }
  deriving Data

data EpArrow
  = EpU !(EpUniToken "-U>" "-★>")
  | EpA !(EpUniToken "-A>" "-●>")
  | EpL !(EpUniToken "-L>" "-○>")
  | EpVar !(LocatedN RdrName)
  deriving Data

type instance XCsArrow Ps = EpArrow
type instance XCsArrow Rn = NoExtField
type instance XCsArrow Tc = NoExtField

instance (OutputableBndrId p) => Outputable (CsArrow (CsPass p)) where
  ppr arr = parens (pprCsArrow arr)

pprCsArrow :: (OutputableBndrId p) => CsArrow (CsPass p) -> SDoc
pprCsArrow (CsArrow _ kind) = ppr kind

csTyVarLName :: CsTyVarBndr (CsPass p) -> LIdP (CsPass p)
csTyVarLName (KindedTyVar _ n _) = n
csTyVarLName (ImpKindedTyVar _ n _) = n

csTyVarName :: CsTyVarBndr (CsPass p) -> IdP (CsPass p)
csTyVarName = unLoc . csTyVarLName

csLTyVarLocName
  :: Anno (IdCsP p) ~ SrcSpanAnnN => LCsTyVarBndr (CsPass p) -> LocatedN (IdP (CsPass p))
csLTyVarLocName (L _ a) = csTyVarLName a

{- *********************************************************************
*                                                                      *
                Building types
*                                                                      *
********************************************************************* -}

mkCsOpTy
  :: (Anno (IdCsP p) ~ SrcSpanAnnN)
  => LCsType (CsPass p)
  -> LocatedN (IdP (CsPass p))
  -> LCsType (CsPass p)
  -> CsType (CsPass p)
mkCsOpTy ty1 op ty2 = CsOpTy noAnn ty1 op ty2

mkCsAppTy :: LCsType (CsPass p) -> LCsType (CsPass p) -> LCsType (CsPass p)
mkCsAppTy t1 t2 = addCLocA t1 t2 (CsAppTy noExtField t1 t2)

{- *********************************************************************
*                                                                      *
            OpName
*                                                                      *
********************************************************************* -}

data OpName
  = NormalOp Name
  | NegateOp
  | UnboundOp RdrName

instance Outputable OpName where
  ppr (NormalOp n) = ppr n
  ppr NegateOp = ppr negateName
  ppr (UnboundOp uv) = ppr uv

{- *********************************************************************
*                                                                      *
            Pretty printing
*                                                                      *
********************************************************************* -}
-- class OutputableBndrFlag p where
--   pprTyVarBndr :: OutputableBndrId p => CsTyVarBndr (CsPass p) -> SDoc

instance OutputableBndrId p => Outputable (CsSigType (CsPass p)) where
  ppr (CsSig{ sig_body = body }) = ppr body

instance OutputableBndrId p => Outputable (CsType (CsPass p)) where
  ppr ty = pprCsType ty

instance (OutputableBndrId p) => Outputable (CsTyVarBndr (CsPass p)) where
  ppr (KindedTyVar _ n k) = parens $ hsep [ppr n, colon, ppr k]
  ppr (ImpKindedTyVar _ n k) = braces $ hsep [ppr n, colon, ppr k]

instance (OutputableBndrId p) => Outputable (CsPatSigType (CsPass p)) where
  ppr (CsPS { csps_body = ty }) = ppr ty

instance (OutputableBndrId p) => Outputable (CsTyPat (CsPass p)) where
  ppr (CsTP { cstp_body = ty }) = ppr ty

pprCsForAll
  :: (OutputableBndrId p)
  => CsForAllTelescope (CsPass p)
  -> SDoc
pprCsForAll (CsForAll {csf_bndrs = qtvs})
  | null qtvs = whenPprDebug (forAllLit <> dot)
  | otherwise = forAllLit <+> interppSP qtvs <> dot

pprCsType :: (OutputableBndrId p) => CsType (CsPass p) -> SDoc
pprCsType ty = ppr_mono_ty ty

ppr_mono_lty :: (OutputableBndrId p) => LCsType (CsPass p) -> SDoc
ppr_mono_lty ty = ppr_mono_ty (unLoc ty)

ppr_mono_ty :: (OutputableBndrId p) => CsType (CsPass p) -> SDoc
ppr_mono_ty (CsForAllTy {cst_tele = tele, cst_body = ty})
  = sep [pprCsForAll tele, ppr_mono_lty ty]
ppr_mono_ty (CsQualTy _ ctxt ty) = sep [text "ppr_mono_ty CTXT", ppr_mono_lty ty]
ppr_mono_ty (CsTyVar _ (L _ name)) = pprPrefixOcc name
ppr_mono_ty (CsUnboundTyVar _ v) = pprPrefixOcc v
ppr_mono_ty (CsAppTy _ fun_ty arg_ty)
  = hsep [ppr_mono_lty fun_ty, ppr_mono_lty arg_ty]
ppr_mono_ty (CsFunTy _ mult ty1 ty2) = ppr_fun_ty mult ty1 ty2
ppr_mono_ty (CsTupleTy _ tys) = parens (fcat (ppr_tup_args tys))
  where
    ppr_tup_args [] = []
    ppr_tup_args (TyPresent _ t : ts)
      = (ppr_mono_lty t <> punc ts) : ppr_tup_args ts
    ppr_tup_args (TyMissing _ : ts)
      = punc ts : ppr_tup_args ts
    punc (TyPresent{} : _) = comma <> space
    punc (TyMissing{} : _) = comma
    punc [] = empty
ppr_mono_ty (CsSumTy _ tys) = parens (pprWithBars ppr tys)
ppr_mono_ty (CsOpTy _ ty1 (L _ op) ty2)
  = sep [ ppr_mono_lty ty1, sep [pprOcc Infix op, ppr_mono_lty ty2 ] ]
ppr_mono_ty (CsParTy _ ty) = parens (ppr_mono_lty ty)
ppr_mono_ty (CsKindSig _ ty kind)
  = ppr_mono_lty ty <+> colon <+> ppr kind
ppr_mono_ty (CsTyLamTy _ _) = text "ppr_mono_ty CsTyLamTy"
ppr_mono_ty (TySectionL _ ty op)
  | Just pp_op <- ppr_infix_ty (unLoc op)
  = pp_infixly pp_op
  | otherwise
  = pp_prefixly
  where
    pp_ty = pprDebugParendTy opPrec ty
    pp_prefixly = hang (hsep [ text " \\ x_ ->", ppr op])
                       4 (hsep [pp_ty, text "x_ )"])
    pp_infixly v = sep [v, pp_ty]
ppr_mono_ty (TySectionR _ op ty)
  | Just pp_op <- ppr_infix_ty (unLoc op)
  = pp_infixly pp_op
  | otherwise
  = pp_prefixly
  where
    pp_ty = pprDebugParendTy opPrec ty
    pp_prefixly = hang (hsep [ text "( \\ x_ ->"
                             , ppr op
                             , text "x_" ])
                        4 (pp_ty <> rparen)
    pp_infixly v = sep [v, pp_ty]

ppr_infix_ty :: (OutputableBndrId p) => CsType (CsPass p) -> Maybe SDoc
ppr_infix_ty (CsTyVar _ (L _ v)) = Just (pprInfixOcc v)
ppr_infix_ty (CsUnboundTyVar _ v) = Just (pprInfixOcc v)
ppr_infix_ty _ = Nothing

pprDebugParendTy :: (OutputableBndrId p) => PprPrec -> LCsType (CsPass p) -> SDoc
pprDebugParendTy p ty = getPprDebug $ \case
  True -> pprParendLTy p ty
  False -> ppr_mono_lty ty

pprParendLTy :: (OutputableBndrId p) => PprPrec -> LCsType (CsPass p) -> SDoc
pprParendLTy p (L _ e) = pprParendTy p e

pprParendTy :: (OutputableBndrId p) => PprPrec -> CsType (CsPass p) -> SDoc
pprParendTy p ty
  | csTyNeedsParens p ty = parens (pprCsType ty)
  | otherwise = pprCsType ty

csTyNeedsParens :: IsPass p => PprPrec -> CsType (CsPass p) -> Bool
csTyNeedsParens prec = go
  where
    go (CsTyVar{}) = False
    go (CsUnboundTyVar{}) = False
    go (CsTyLamTy{}) = prec > topPrec
    go (CsAppTy{}) = prec >= appPrec
    go (CsOpTy{}) = prec >= opPrec
    go (CsParTy{}) = False
    go (CsFunTy{}) = prec > topPrec
    go (CsTupleTy{}) = False
    go (CsSumTy{}) = False
    go (CsKindSig{}) = True
    go (TySectionL{}) = True
    go (TySectionR{}) = True
    go (CsForAllTy{}) = prec > topPrec
    go (CsQualTy{}) = prec > topPrec

ppr_fun_ty
  :: (OutputableBndrId p)
  => CsArrow (CsPass p)
  -> LCsType (CsPass p)
  -> LCsType (CsPass p)
  -> SDoc
ppr_fun_ty mult ty1 ty2
  = let p1 = ppr_mono_lty ty1
        p2 = ppr_mono_lty ty2
        arr = pprCsArrow mult
    in sep [p1, arr <+> p2]

type instance Anno (CsType (CsPass p)) = SrcSpanAnnA
type instance Anno (CsSigType (CsPass p)) = SrcSpanAnnA

type instance Anno (CsTyVarBndr (CsPass p)) = SrcSpanAnnA
type instance Anno (CsTyVarBndr Ps) = SrcSpanAnnA
type instance Anno (CsTyVarBndr Rn) = SrcSpanAnnA
type instance Anno (CsTyVarBndr Tc) = SrcSpanAnnA
type instance Anno [LocatedA (Match (CsPass p) (LocatedA (CsType (CsPass p))))] = SrcSpanAnnL
type instance Anno (Match (CsPass p) (LocatedA (CsType (CsPass p)))) = SrcSpanAnnA
type instance Anno (GRHS (CsPass p) (LocatedA (CsType (CsPass p)))) = EpAnnCO
