module CSlash.Tc.Utils.TcType where

import CSlash.Utils.Misc (HasDebugCallStack)
import CSlash.Utils.Outputable (SDoc)

data TcTyVarDetails

data TcKiVarDetails

pprTcTyVarDetails :: TcTyVarDetails -> SDoc

vanillaSkolemTvUnk :: HasDebugCallStack => TcTyVarDetails