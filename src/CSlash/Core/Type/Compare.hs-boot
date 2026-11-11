{-# LANGUAGE FlexibleContexts #-}

module CSlash.Core.Type.Compare where

import {-# SOURCE #-} CSlash.Core.Rep
import CSlash.Cs.Pass
import CSlash.Utils.Misc

eqMonoKind :: (HasCallStack, HasPass p pass) => MonoKind p -> MonoKind p -> Bool
