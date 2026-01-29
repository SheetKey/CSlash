module CSlash.Core.Kind.Compare where

import {-# SOURCE #-} CSlash.Core.Kind (Kind, MonoKind)
import CSlash.Utils.Misc (HasCallStack, HasDebugCallStack)

tcEqKind :: (HasDebugCallStack) => Kind p -> Kind p -> Bool
eqMonoKind :: (HasCallStack) => MonoKind p -> MonoKind p -> Bool