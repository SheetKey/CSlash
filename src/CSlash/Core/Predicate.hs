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

data TyPred tv kv
  = TyEqPred (Type tv kv) (Type tv kv)
  | TyIrredPred (PredType tv kv)

classifyPredType :: IsTyVar tv kv => PredType tv kv -> TyPred tv kv
classifyPredType ev_ty = case splitTyConApp_maybe ev_ty of
  Just (tc, [_, _, ty1, ty2])
    | tc `hasKey` eqTyConKey -> TyEqPred ty1 ty2
  _ -> TyIrredPred ev_ty

isTyCoVarType :: IsTyVar tv kv => Type tv kv -> Bool
isTyCoVarType ty = isTyEqPred ty

isTyEqPred :: IsTyVar tv kv => Type tv kv -> Bool
isTyEqPred ty
  | Just tc <- tyConAppTyCon_maybe ty
  = tc `hasKey` eqTyConKey
  | otherwise
  = False

getPredTys :: IsTyVar tv kv => PredType tv kv -> (Type tv kv, Type tv kv)
getPredTys ty = case getPredTys_maybe ty of
                  Just tys -> tys
                  Nothing -> pprPanic "getPredTys" (ppr ty)

getPredTys_maybe :: IsTyVar tv kv => PredType tv kv -> Maybe (Type tv kv, Type tv kv)
getPredTys_maybe ty = case splitTyConApp_maybe ty of
                        Just (tc, [_, _, ty1, ty2]) | tc `hasKey` eqTyConKey -> Just (ty1, ty2)
                        _ -> Nothing

data KiPred kv
  = KiCoPred KiPredCon (MonoKind kv) (MonoKind kv)
  | IrredPred (PredKind kv)

classifyPredKind :: PredKind kv -> KiPred kv
classifyPredKind ev_ki = case ev_ki of
  KiPredApp pred ki1 ki2 -> KiCoPred pred ki1 ki2
  _ -> IrredPred ev_ki

getPredKis :: Outputable kv => PredKind kv -> (KiPredCon, MonoKind kv, MonoKind kv)
getPredKis (KiPredApp pred k1 k2) = (pred, k1, k2)
getPredKis other = pprPanic "getPredKis" (ppr other)

getPredKis_maybe :: PredKind kv -> Maybe (KiPredCon, MonoKind kv, MonoKind kv)
getPredKis_maybe (KiPredApp pred k1 k2) = Just (pred, k1, k2)
getPredKis_maybe _ = Nothing

mkRelPred :: KiPredCon -> MonoKind kv -> MonoKind kv -> PredKind kv
mkRelPred = mkKiPredApp
