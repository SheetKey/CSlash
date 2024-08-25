{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module CSlash.Cs.Kind
  ( module CSlash.Language.Syntax.Kind
  , module CSlash.Cs.Kind
  ) where

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Kind
import CSlash.Cs.Extension
import CSlash.Types.SrcLoc
import CSlash.Types.Name
import CSlash.Parser.Annotation
import CSlash.Utils.Outputable

import Data.Data

type instance XCsPSK Ps = EpAnnCO
type instance XCsPSK Rn = CsPSKRn
type instance XCsPSK Tc = CsPSKRn

data CsPSKRn = CsPSKRn
  { cspsk_nwcs :: [Name]
  , cspsk_imp_kvs :: [Name]
  }
  deriving Data

type instance XUKd (CsPass _) = NoExtField
type instance XAKd (CsPass _) = NoExtField
type instance XLKd (CsPass _) = NoExtField
type instance XKdVar (CsPass _) = [AddEpAnn]
type instance XFunKd (CsPass _) = NoExtField
type instance XQualKd (CsPass _) = NoExtField
type instance XParKd (CsPass _) = NoExtField

-- type instance XKdLT Ps = EpToken "<"
type instance XKdLT (CsPass _) = EpToken "<"
type instance XKdLTEQ (CsPass _) = EpToken "<="

instance (OutputableBndrId p) => Outputable (CsKind (CsPass p)) where
  ppr kind = pprCsKind kind

pprCsKind :: (OutputableBndrId p) => CsKind (CsPass p) -> SDoc
pprCsKind kind = ppr_kind kind

ppr_lkind :: (OutputableBndrId p) => LCsKind (CsPass p) -> SDoc
ppr_lkind kind = ppr_kind (unLoc kind)

ppr_kind :: (OutputableBndrId p) => CsKind (CsPass p) -> SDoc
ppr_kind (CsUKd _) = uKindLit
ppr_kind (CsAKd _) = aKindLit
ppr_kind (CsLKd _) = lKindLit
ppr_kind (CsKdVar _ (L _ name)) = pprPrefixOcc name
ppr_kind (CsFunKd _ kd1 kd2)
  = sep [ppr_lkind kd1, arrow <+> ppr_lkind kd2]
ppr_kind (CsQualKd{ csk_ctxt = ctxt, csk_body = kind })
  = sep [pprLCsContextAlways ctxt, ppr_lkind kind]
ppr_kind (CsParKd _ kind) = parens (ppr_lkind kind)

pprLCsContextAlways
  :: (OutputableBndrId p)
  => LCsContext (CsPass p) -> SDoc
pprLCsContextAlways (L _ ctxt)
  = case ctxt of
      [] -> parens empty <+> darrow
      [L _ rel] -> ppr_kdrel rel <+> darrow
      _ -> parens (interpp'SP ctxt) <+> darrow

instance (OutputableBndrId p) => Outputable (CsKdRel (CsPass p)) where
  ppr rel = pprCsKdRel rel

pprCsKdRel
  :: (OutputableBndrId p)
  => CsKdRel (CsPass p)
  -> SDoc
pprCsKdRel rel = ppr_kdrel rel

ppr_lkdrel
  :: (OutputableBndrId p)
  => LCsKdRel (CsPass p)
  -> SDoc
ppr_lkdrel lkdrel = ppr_kdrel (unLoc lkdrel)

ppr_kdrel
  :: (OutputableBndrId p)
  => CsKdRel (CsPass p)
  -> SDoc
ppr_kdrel (CsKdLT _ kd1 kd2) 
  = sep [ppr_lkind kd1, char '<', ppr_lkind kd2]
ppr_kdrel (CsKdLTEQ _ kd1 kd2)
  = sep [ppr_lkind kd1, text "<=", ppr_lkind kd2]

type instance Anno (CsKind (CsPass p)) = SrcSpanAnnA

type instance Anno (CsKdRel (CsPass p)) = SrcSpanAnnA

type instance Anno [LocatedA (CsKdRel (CsPass p))] = SrcSpanAnnC
