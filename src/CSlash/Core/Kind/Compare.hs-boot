module CSlash.Core.Kind.Compare where

import CSlash.Core.Kind (Kind)
import CSlash.Utils.Misc (HasDebugCallStack)
import CSlash.Types.Var (VarHasUnique)

tcEqKind :: (HasDebugCallStack, Eq kv, VarHasUnique kv) => Kind kv -> Kind kv -> Bool