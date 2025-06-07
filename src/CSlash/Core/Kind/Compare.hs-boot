module CSlash.Core.Kind.Compare where

import CSlash.Core.Kind (Kind)
import CSlash.Utils.Misc (HasDebugCallStack)

tcEqKind :: HasDebugCallStack => Kind kv -> Kind kv -> Bool
