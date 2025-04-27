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

data Pred
  = EqPred MonoKind MonoKind
  | RelPred KiCon MonoKind MonoKind
  | IrredPred PredKind

classifyPredKind :: PredKind -> Pred
classifyPredKind ev_ki = case ev_ki of
  KiConApp kc [ki1, ki2]
    | kc == EQKi -> EqPred ki1 ki2
    | otherwise -> RelPred kc ki1 ki2
  _ -> IrredPred ev_ki

mkRelPred :: KiCon -> MonoKind -> MonoKind -> PredKind
mkRelPred kc ki1 ki2 = mkKiConApp kc [ki1, ki2]
