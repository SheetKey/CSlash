module CSlash.CsToCore.Binds where

import CSlash.Cs.Pass
import CSlash.CsToCore.Monad (DsM)
import CSlash.Core (CoreExpr)
import CSlash.Tc.Types.Evidence (CsWrapper)

dsCsWrapper :: CsWrapper Zk -> ((CoreExpr -> CoreExpr) -> DsM a) -> DsM a