module CSlash.Core.Kind.Compare where

import CSlash.Core.Kind (Kind)
import CSlash.Utils.Misc (HasDebugCallStack)
import CSlash.Types.Var (IsVar)

tcEqKind :: (HasDebugCallStack, IsVar kv) => Kind kv -> Kind kv -> Bool