module CSlash.Tc.Gen.Expr where

import CSlash.Cs (CsExpr, LCsExpr)
import CSlash.Tc.Utils.TcType (AnyRhoType, ExpSigmaType, ExpRhoType)
import CSlash.Tc.Types (TcM)
import CSlash.Cs.Extension (Rn, Tc)

tcPolyLExpr :: LCsExpr Rn -> ExpSigmaType -> TcM (LCsExpr Tc)
tcPolyExpr :: CsExpr Rn -> ExpSigmaType -> TcM (CsExpr Tc) 

tcInferRhoNC :: LCsExpr Rn -> TcM (LCsExpr Tc, AnyRhoType)

tcCheckMonoExpr :: LCsExpr Rn -> AnyRhoType -> TcM (LCsExpr Tc)

tcExpr :: CsExpr Rn -> ExpRhoType -> TcM (CsExpr Tc)
