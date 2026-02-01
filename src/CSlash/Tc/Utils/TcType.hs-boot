module CSlash.Tc.Utils.TcType where

import CSlash.Utils.Misc (HasDebugCallStack)
import CSlash.Utils.Outputable (SDoc)

data TcVarDetails tk

pprTcVarDetails :: TcVarDetails tk -> SDoc

vanillaSkolemVarUnk :: HasDebugCallStack => TcVarDetails tk