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

import CSlash.Types.RepType
-- import CSlash.Types.Name ( isDynLinkName )
import CSlash.Unit.Module ( Module )
import CSlash.Stg.Syntax

import CSlash.Utils.Outputable

import CSlash.Utils.Panic

import CSlash.Data.FastString

mkUnarisedIds :: MonadUnique m => FastString -> [NvUnaryType] -> m [CoreId]
mkUnarisedIds fs tys = mapM (mkUnarisedId fs) tys

mkUnarisedId :: MonadUnique m => FastString -> NvUnaryType -> m CoreId
mkUnarisedId s t = mkSysLocalM s t

bindersOf :: BinderP a ~ CoreId => GenStgBinding a -> [CoreId]
bindersOf (StgNonRec binder _) = [binder]
bindersOf (StgRec pairs) = fst <$> pairs

stripStgTicksTop :: (StgTickish -> Bool) -> GenStgExpr p -> ([StgTickish], GenStgExpr p)
stripStgTicksTop p = go []
  where
    go ts (StgTick t e) | p t = go (t : ts) e
    go [] other = ([], other)
    go ts other = (reverse ts, other)

allowTopLevelConApp
  :: Platform
  -> Bool
  -> Module
  -> CoreDataCon
  -> [StgArg]
  -> Bool
allowTopLevelConApp = panic "allowTopLevelConApp"
