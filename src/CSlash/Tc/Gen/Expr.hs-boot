module CSlash.Tc.Gen.Expr where

import CSlash.Cs (CsExpr, LCsExpr)
import CSlash.Tc.Utils.TcType (RhoType, ExpSigmaType, ExpRhoType)
import CSlash.Tc.Types (TcM)
import CSlash.Tc.Types.BasicTypes (TcCompleteSig)
import CSlash.Cs.Extension (Rn, Tc)

tcPolyLExpr :: LCsExpr Rn -> ExpSigmaType -> TcM (LCsExpr Tc)
tcPolyExpr :: CsExpr Rn -> ExpSigmaType -> TcM (CsExpr Tc) 

tcPolyLExprSig :: LCsExpr Rn -> TcCompleteSig -> TcM (LCsExpr Tc)

tcInferRhoNC :: LCsExpr Rn -> TcM (LCsExpr Tc, RhoType Tc)

tcCheckMonoExpr :: LCsExpr Rn -> RhoType Tc -> TcM (LCsExpr Tc)

tcExpr :: CsExpr Rn -> ExpRhoType -> TcM (CsExpr Tc)
