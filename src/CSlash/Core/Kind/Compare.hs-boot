module CSlash.Core.Kind.Compare where

import CSlash.Cs.Pass

import {-# SOURCE #-} CSlash.Core.Kind (Kind, MonoKind)
import CSlash.Utils.Misc (HasCallStack, HasDebugCallStack)

tcEqKind :: (HasDebugCallStack, HasPass p p') => Kind p -> Kind p -> Bool
eqMonoKind :: (HasCallStack, HasPass p pass) => MonoKind p -> MonoKind p -> Bool