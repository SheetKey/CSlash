module CSlash.Tc.Gen.Match where

import CSlash.Cs (MatchGroup, CsExpr, LCsExpr)
import CSlash.Tc.Utils.TcType (ExpSigmaType, ExpPatType)
import CSlash.Tc.Types (TcM)
import CSlash.Tc.Types.Evidence (CsWrapper)
import CSlash.Cs.Extension (Rn, Tc)

tcLambdaMatches
  :: CsExpr Rn
  -> MatchGroup Rn (LCsExpr Rn)
  -> [ExpPatType]
  -> ExpSigmaType
  -> TcM (CsWrapper Tc, MatchGroup Tc (LCsExpr Tc))
