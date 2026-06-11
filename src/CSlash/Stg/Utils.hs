module CSlash.Stg.Utils where

import CSlash.Platform
import CSlash.Core (CoreId)

import CSlash.Types.Var.Id
import CSlash.Core.Type
import CSlash.Core.TyCon
import CSlash.Core.DataCon
import CSlash.Core
import CSlash.Types.Tickish
import CSlash.Types.Unique.Supply

-- import GHC.Types.RepType
-- import CSlash.Types.Name ( isDynLinkName )
import CSlash.Unit.Module ( Module )
import CSlash.Stg.Syntax

import CSlash.Utils.Outputable

import CSlash.Utils.Panic

import CSlash.Data.FastString

bindersOf :: BinderP a ~ CoreId => GenStgBinding a -> [CoreId]
bindersOf (StgNonRec binder _) = [binder]
bindersOf (StgRec pairs) = fst <$> pairs

allowTopLevelConApp
  :: Platform
  -> Bool
  -> Module
  -> CoreDataCon
  -> [StgArg]
  -> Bool
allowTopLevelConApp = panic "allowTopLevelConApp"
