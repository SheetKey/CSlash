{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module CSlash.Cs.Type
  ( CsType(..)
  , CsForAllTelescope(..), CsTyVarBndr(..), LCsTyVarBndr
  , CsPatSigType(..)
  , CsTyPat(..)
  , CsSigType(..)
  , module CSlash.Cs.Type
  ) where

import Prelude hiding ((<>))

import CSlash.Language.Syntax.Type
import CSlash.Language.Syntax.Extension
import CSlash.Cs.Extension
import CSlash.Cs.Kind
import CSlash.Types.SrcLoc
import CSlash.Parser.Annotation
import CSlash.Utils.Outputable

instance (OutputableBndrId p) => Outputable (CsArrow (CsPass p)) where
  ppr arr = parens (pprCsArrow arr)

pprCsArrow :: (OutputableBndrId p) => CsArrow (CsPass p) -> SDoc
pprCsArrow (CsArrow _ kind) = ppr kind

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
pprCsForAll (CsForAllInvis {csf_invis_bndrs = qtvs})
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
