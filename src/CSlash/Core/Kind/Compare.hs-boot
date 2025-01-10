module CSlash.Core.Kind.Compare where

import CSlash.Core.Kind (Kind)
import CSlash.Utils.Misc (HasDebugCallStack)

tcEqKind :: HasDebugCallStack => Kind -> Kind -> Bool
