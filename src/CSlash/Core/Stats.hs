module CSlash.Core.Stats where

import CSlash.Types.Basic
import CSlash.Core
import CSlash.Utils.Outputable
-- import CSlash.Core.Coercion
import CSlash.Types.Tickish
import CSlash.Types.Var
import CSlash.Core.Type(Type{-, typeSize-})
import CSlash.Types.Var.Id (isJoinId)

data CoreStats = CS

instance Outputable CoreStats where
  ppr CS = text "CORE STATS NOT IMPLEMENTED"

coreBindsStats :: [CoreBind] -> CoreStats
coreBindsStats _ = CS
