{-# LANGUAGE FlexibleInstances #-}

module CSlash.Core.Ppr where

import CSlash.Cs.Pass

import {-# SOURCE #-} CSlash.Core
import {-# SOURCE #-} CSlash.Types.Var (Id)
import CSlash.Utils.Outputable (OutputableBndr, Outputable)

instance OutputableBndr b => Outputable (Expr b)

instance IsPass p => OutputableBndr (Id (CsPass p))