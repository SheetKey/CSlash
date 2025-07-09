module CSlash.Core.Predicate where

import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.TyCon
import CSlash.Types.Var

import CSlash.Builtin.Names

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Data.FastString

data Pred kv
  = KiCoPred KiPred (MonoKind kv) (MonoKind kv)
  | IrredPred (PredKind kv)

classifyPredKind :: PredKind kv -> Pred kv
classifyPredKind ev_ki = case ev_ki of
  KiPredApp pred ki1 ki2 -> KiCoPred pred ki1 ki2
  _ -> IrredPred ev_ki

getPredKis :: Outputable kv => PredKind kv -> (KiPred, MonoKind kv, MonoKind kv)
getPredKis (KiPredApp pred k1 k2) = (pred, k1, k2)
getPredKis other = pprPanic "getPredKis" (ppr other)

getPredKis_maybe :: PredKind kv -> Maybe (KiPred, MonoKind kv, MonoKind kv)
getPredKis_maybe (KiPredApp pred k1 k2) = Just (pred, k1, k2)
getPredKis_maybe _ = Nothing

mkRelPred :: KiPred -> MonoKind kv -> MonoKind kv -> PredKind kv
mkRelPred = mkKiPredApp
