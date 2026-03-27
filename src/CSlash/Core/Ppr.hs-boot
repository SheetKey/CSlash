{-# LANGUAGE FlexibleInstances #-}

module CSlash.Core.Ppr where

import CSlash.Cs.Pass

import {-# SOURCE #-} CSlash.Core
import {-# SOURCE #-} CSlash.Types.Var.Id (Id)
import CSlash.Utils.Outputable (OutputableBndr, Outputable)

instance (OutputableBndr b1, OutputableBndr b2) => Outputable (Expr b1 b2)

instance IsPass p => OutputableBndr (Id (CsPass p))