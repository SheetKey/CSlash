module CSlash.Tc.Gen.Bind where

import CSlash.Tc.Types.Origin
import CSlash.Types.Name
import CSlash.Cs
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Types

tcFunBind
  :: UserTypeCtxt
  -> Name
  -> LCsExpr Rn
  -> [ExpPatType] -- all invis
  -> ExpRhoType
  -> TcM (CsWrapper Tc, LCsExpr Tc)
