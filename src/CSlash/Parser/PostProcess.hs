module CSlash.Parser.PostProcess where

import CSlash.Cs

import CSlash.Types.SrcLoc
import CSlash.Types.Name.Reader

-- mkTySynonym in GHC
mkTyFunBind
  :: SrcSpan
  -> Located RdrName
  -> LCsType Ps
  -> [AddEpAnn]
  -> P (LCsBind Ps)
mkTyFunBind loc name rhs annsIn = return (L loc (TyFunBind annsIn name rhs))

-- mkFunBind
--   :: SrcSpan
--   -> Located RdrName
--   -> LCsExpr Ps
--   -> AddEpAnn
--   -> P (LCsBind Ps)
-- mkFunBind loc name rhs annsIn = return (L loc (VarBind annsIn name rhs))

checkPrecP
  :: Located (SourceText, Int)
  -> LocatedN RdrName
  -> P ()
checkPrecP (L l (_, i)) (L _ op)
  | 0 <= i, i <= maxPrecedence = pure ()
  | specialOp op = pure ()
  | otherwise = addFatalError $ mkPlainErrorMsgEnvelope l (PsErrPrecedenceOutOfRange i)
  where
    specialOp op = unLoc op == getRdrName unrestrictedFunTyCon -- should check for any arrow
