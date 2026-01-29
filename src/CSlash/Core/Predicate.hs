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

data TyPred p
  = TyEqPred (Type p) (Type p)
  | TyIrredPred (PredType p)
  | ForAllPred [TyVar p] (PredType p)

classifyPredType :: PredType p -> TyPred p
classifyPredType ev_ty = case splitTyConApp_maybe ev_ty of
  Just (tc, [_, _, ty1, ty2])
    | tc `hasKey` eqTyConKey -> TyEqPred ty1 ty2

  _ | (tvs, rho) <- splitForAllTyVars ev_ty
    , not (null tvs)
    -> ForAllPred tvs rho

  _ -> TyIrredPred ev_ty

isTyCoVarType :: Type p -> Bool
isTyCoVarType ty = isTyEqPred ty

isTyEqPred :: Type p -> Bool
isTyEqPred ty
  | Just tc <- tyConAppTyCon_maybe ty
  = tc `hasKey` eqTyConKey
  | otherwise
  = False

getPredTys :: PredType p -> (Type p, Type p)
getPredTys ty = case getPredTys_maybe ty of
                  Just tys -> tys
                  Nothing -> pprPanic "getPredTys" (ppr ty)

getPredTys_maybe :: PredType p -> Maybe (Type p, Type p)
getPredTys_maybe ty = case splitTyConApp_maybe ty of
                        Just (tc, [_, _, ty1, ty2]) | tc `hasKey` eqTyConKey -> Just (ty1, ty2)
                        _ -> Nothing

data KiPred p
  = KiCoPred KiPredCon (MonoKind p) (MonoKind p)
  | IrredPred (PredKind p)

classifyPredKind :: PredKind p -> KiPred p
classifyPredKind ev_ki = case ev_ki of
  KiPredApp pred ki1 ki2 -> KiCoPred pred ki1 ki2
  _ -> IrredPred ev_ki

getPredKis :: PredKind p -> (KiPredCon, MonoKind p, MonoKind p)
getPredKis (KiPredApp pred k1 k2) = (pred, k1, k2)
getPredKis other = pprPanic "getPredKis" (ppr other)

getPredKis_maybe :: PredKind p -> Maybe (KiPredCon, MonoKind p, MonoKind p)
getPredKis_maybe (KiPredApp pred k1 k2) = Just (pred, k1, k2)
getPredKis_maybe _ = Nothing

mkRelPred :: KiPredCon -> MonoKind p -> MonoKind p -> PredKind p
mkRelPred = mkKiPredApp
