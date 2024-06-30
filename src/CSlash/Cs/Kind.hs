module CSlash.Cs.Kind where

import CSlash.Language.Syntax.Extension
import CSlash.Language.Syntax.Kind
import CSlash.Cs.Extension

instance (OutputableBndrId p) => Outputable (CsKind (CsPass p)) where
  ppr kind = pprCsKind kind

pprCsKind :: (OutputableBndrId p) => CsKind (CsPass p) -> SDoc
pprCsKind kind = ppr_kind kind

ppr_lkind :: (OutputableBndrId p) => LCsKind (CsPass p) -> SDoc
ppr_lkind kind = ppr_kind (unLoc kind)

ppr_kind :: (OutputableBndrId p) => CsType (CsPass p) -> SDoc
ppr_kind (CsUkd _) = uKindLit
ppr_kind (CsAKd _) = aKindLit
ppr_kind (CsLKd _) = lKindLit
ppr_kind (CsKdVar _ (L _ name)) = pprOccWithTick Prefix name
ppr_kind (CsFunKind _ kd1 kd2)
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
      [L _ kind] -> ppr_kind kind <+> darrow
      _ -> parens (interpp'SP ctxt) <+> darrow

instance (OutputableBndrId p) => Outputable (CsKdRel (CsPass p)) where
  ppr rel = pprCsKdRel rel

pprCsKdRel
  :: (OutputableBndrId p)
  => Outputable (CsKdRel (CsPass p))
  -> SDoc
pprCsKdRel rel = ppr_kdrel rel

ppr_lkdrel
  :: (OutputableBndrId p)
  => Outputable (LCsKdRel (CsPass p))
  -> SDoc
ppr_lkdrel lkdrel = ppr_kdrel (unLoc lkdrel)

ppr_kdrel
  :: (OutputableBndrId p)
  -> Outputable (CsKdRel (CsPass p))
  -> SDoc
ppr_kdrel (CsKdLT _ kd1 kd2) 
  = sep [ppr_lkind kd1, char '<', ppr_lkind kd2]
ppr_kdrel (CsKdLTEQ _ kd1 kd2)
  = sep [ppr_lkind kd1, text "<=", ppr_lkind kd2]
