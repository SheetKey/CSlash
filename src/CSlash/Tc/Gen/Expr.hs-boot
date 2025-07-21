module CSlash.Tc.Gen.Expr where

import CSlash.Cs (LCsExpr)
import CSlash.Tc.Utils.TcType (AnyRhoType, ExpSigmaType)
import CSlash.Tc.Types (TcM)
import CSlash.Cs.Extension (Rn, Tc)

tcPolyLExpr :: LCsExpr Rn -> ExpSigmaType -> TcM (LCsExpr Tc)

tcInferRhoNC :: LCsExpr Rn -> TcM (LCsExpr Tc, AnyRhoType)

tcCheckMonoExpr :: LCsExpr Rn -> AnyRhoType -> TcM (LCsExpr Tc)
