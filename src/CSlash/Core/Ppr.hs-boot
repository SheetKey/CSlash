module CSlash.Core.Ppr where

import {-# SOURCE #-} CSlash.Core
import {-# SOURCE #-} CSlash.Types.Var (Id)
import CSlash.Utils.Outputable (OutputableBndr, Outputable)

instance OutputableBndr b => Outputable (Expr b)

instance OutputableBndr (Id p)