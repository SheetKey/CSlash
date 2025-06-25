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
  = EqPred (MonoKind kv) (MonoKind kv)
  | RelPred KiCon (MonoKind kv) (MonoKind kv)
  | IrredPred (PredKind kv)

classifyPredKind :: PredKind kv -> Pred kv
classifyPredKind ev_ki = case ev_ki of
  KiConApp kc [ki1, ki2]
    | kc == EQKi -> EqPred ki1 ki2
    | otherwise -> RelPred kc ki1 ki2
  _ -> IrredPred ev_ki

getKiEqPredKis :: Outputable kv => PredKind kv -> (MonoKind kv, MonoKind kv)
getKiEqPredKis (KiConApp EQKi [k1, k2]) = (k1, k2)
getKiEqPredKis other = pprPanic "getKiEqPredKis" (ppr other)

getKiEqPredKis_maybe :: PredKind kv -> Maybe (MonoKind kv, MonoKind kv)
getKiEqPredKis_maybe (KiConApp EQKi [k1, k2]) = Just (k1, k2)
getKiEqPredKis_maybe _ = Nothing

getPredKcKis :: Outputable kv => PredKind kv -> (KiCon, [MonoKind kv])
getPredKcKis (KiConApp kc kis) = (kc, kis)
getPredKcKis other = pprPanic "getPredKcKis" (ppr other)

getPredKcKis_maybe :: PredKind kv -> Maybe (KiCon, [MonoKind kv])
getPredKcKis_maybe (KiConApp kc kis) = Just (kc, kis)
getPredKcKis_maybe _ = Nothing

mkRelPred :: KiCon -> MonoKind kv -> MonoKind kv -> PredKind kv
mkRelPred kc ki1 ki2 = mkKiConApp kc [ki1, ki2]

isKiEqPred :: PredKind kv -> Bool
isKiEqPred (KiConApp EQKi _) = True
isKiEqPred _ = False
