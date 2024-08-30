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

  , CsConDetails(..)

  , module CSlash.Cs.Type
  ) where

import Prelude hiding ((<>))

import CSlash.Language.Syntax.Type
import {-# SOURCE #-} CSlash.Language.Syntax.Expr
import CSlash.Language.Syntax.Extension
import CSlash.Cs.Extension
import CSlash.Cs.Kind
import CSlash.Types.SrcLoc
import CSlash.Types.Name
import CSlash.Types.Name.Reader
import CSlash.Parser.Annotation
import CSlash.Utils.Outputable

import Data.Data

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
  { csps_nwcs :: [Name]
  , csps_imp_tvs :: [Name]
  }
  deriving Data

data CsTyPatRn = CsTPRn
  { cstp_nwcs :: [Name]
  , cstp_imp_tvs :: [Name]
  , cstp_exp_tvs :: [Name]
  }
  deriving Data

type instance XCsSig (CsPass _) = NoExtField

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
type instance XAppTy (CsPass _) = NoExtField
type instance XFunTy (CsPass _) = NoExtField
type instance XTupleTy (CsPass _) = AnnParen
type instance XSumTy (CsPass _) = AnnParen
type instance XOpTy (CsPass _) = [AddEpAnn]
type instance XParTy (CsPass _) = AnnParen
type instance XKdSig (CsPass _) = [AddEpAnn]
type instance XTyLamTy (CsPass _) = [AddEpAnn]

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
ppr_mono_ty (CsTyVar _ (L _ name)) = pprPrefixOcc name
ppr_mono_ty (CsAppTy _ fun_ty arg_ty)
  = hsep [ppr_mono_lty fun_ty, ppr_mono_lty arg_ty]
ppr_mono_ty (CsFunTy _ mult ty1 ty2) = ppr_fun_ty mult ty1 ty2
ppr_mono_ty (CsTupleTy _ tys) = parens (pprWithCommas ppr tys)
ppr_mono_ty (CsSumTy _ tys) = parens (pprWithBars ppr tys)
ppr_mono_ty (CsParTy _ ty) = parens (ppr_mono_lty ty)
ppr_mono_ty (CsKindSig _ ty kind)
  = ppr_mono_lty ty <+> colon <+> ppr kind

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
