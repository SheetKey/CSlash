module CSlash.Core.Ppr where

import {-# SOURCE #-} CSlash.Core
import {-# SOURCE #-} CSlash.Types.Var (Var)
import CSlash.Utils.Outputable (OutputableBndr, Outputable)

instance OutputableBndr b => Outputable (Expr b)

instance OutputableBndr Var