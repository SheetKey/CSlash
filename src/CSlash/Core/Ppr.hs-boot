module CSlash.Core.Ppr where

import {-# SOURCE #-} CSlash.Core
import {-# SOURCE #-} CSlash.Types.Var (Var)
import CSlash.Utils.Outputable (OutputableBndr, Outputable)
import CSlash.Types.Var (IsTyVar)

instance OutputableBndr b => Outputable (Expr b)

instance IsTyVar tv kv => OutputableBndr (Var tv kv)