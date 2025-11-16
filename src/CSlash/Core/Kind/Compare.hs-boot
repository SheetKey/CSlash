module CSlash.Core.Kind.Compare where

import {-# SOURCE #-} CSlash.Core.Kind (Kind, MonoKind)
import CSlash.Utils.Misc (HasCallStack, HasDebugCallStack)
import CSlash.Types.Var (IsVar)

tcEqKind :: (HasDebugCallStack, IsVar kv) => Kind kv -> Kind kv -> Bool
eqMonoKind :: (HasCallStack, IsVar kv) => MonoKind kv -> MonoKind kv -> Bool