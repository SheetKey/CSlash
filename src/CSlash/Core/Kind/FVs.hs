{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE ExplicitForAll #-}

module CSlash.Core.Kind.FVs where

import {-# SOURCE #-} CSlash.Core.Type.FVs (fvsOfType)

import CSlash.Cs.Pass

import Data.Monoid as DM ( Endo(..), Any(..) )
import CSlash.Core.Rep
import CSlash.Core.Kind
import CSlash.Core.TyCon

import CSlash.Types.Var
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Set
import CSlash.Types.Unique

import CSlash.Types.Var.Set
import CSlash.Types.Var.Env
import CSlash.Utils.Misc
import CSlash.Utils.FV
import CSlash.Utils.Panic
import CSlash.Utils.Outputable
  
{- *********************************************************************
*                                                                      *
          The FV versions return deterministic results
*                                                                      *
********************************************************************* -}

type KiFV p = FV (Kind p)

varsOfKindDSet :: Kind p -> DKiVarSet p
varsOfKindDSet ki = mkDVarSet $ fst $ fvVarAcc $ fvsOfKind ki

varsOfKindList :: Kind p -> [KiVar p]
varsOfKindList ki = fst $ fvVarAcc $ fvsOfKind ki

varsOfMonoKindDSet :: MonoKind p -> DKiVarSet p
varsOfMonoKindDSet ki = mkDVarSet $ fst $ fvVarAcc $ fvsOfMonoKind ki

varsOfMonoKindList :: MonoKind p -> [KiVar p]
varsOfMonoKindList ki = fst $ fvVarAcc $ fvsOfMonoKind ki

varsOfMonoKindsList :: [MonoKind p] -> [KiVar p]
varsOfMonoKindsList kis = fst $ fvVarAcc $ fvsOfMonoKinds kis

fvsOfKind :: Kind p -> KiFV p
fvsOfKind (Mono ki) f bound_vars acc = fvsOfMonoKind ki f bound_vars acc
fvsOfKind (ForAllKi kv ki) f bound_vars acc
  = fvsVarBndr kv (fvsOfKind ki) f bound_vars acc

fvsVarBndrs :: [KiVar p] -> KiFV p -> KiFV p
fvsVarBndrs vars fvs = foldr fvsVarBndr fvs vars

fvsVarBndr :: KiVar p -> KiFV p -> KiFV p
fvsVarBndr kv fvs = delFV kv fvs

fvsOfMonoKind :: MonoKind p -> KiFV p
fvsOfMonoKind (KiVarKi v) f bound_vars (acc_list, acc_set)
  | not (f v) = (acc_list, acc_set)
  | v `elemVarSet` bound_vars = (acc_list, acc_set)
  | v `elemVarSet` acc_set = (acc_list, acc_set)
  | otherwise = (v:acc_list, extendVarSet acc_set v)
fvsOfMonoKind (BIKi{}) f bound_vars acc = acc
fvsOfMonoKind (KiConApp kc) f bound_vars acc = fvsOfKiCon kc f bound_vars acc
fvsOfMonoKind (KiPredApp _ k1 k2) f bound_vars acc
  = (fvsOfMonoKind k1 `unionFV` fvsOfMonoKind k2) f bound_vars acc
fvsOfMonoKind (FunKi _ arg res) f bound_var acc
  = (fvsOfMonoKind arg `unionFV` fvsOfMonoKind res) f bound_var acc

fvsOfMonoKinds :: [MonoKind p] -> KiFV p
fvsOfMonoKinds (ki:kis) fv_cand in_scope acc
  = (fvsOfMonoKind ki `unionFV` fvsOfMonoKinds kis) fv_cand in_scope acc
fvsOfMonoKinds [] fv_cand in_scope acc = emptyFV fv_cand in_scope acc

fvsOfKiCon :: KiCon p -> KiFV p
fvsOfKiCon (KiCon _ base rows) f bound_vars acc
  = (fvsOfMonoKind base `unionFV` fvsOfRowSigs rows) f bound_vars acc

fvsOfRowSigs :: [RowSig p] -> KiFV p
fvsOfRowSigs (r:rs) fv_cand in_scope acc
  = (fvsOfRowSig r `unionFV` fvsOfRowSigs rs) fv_cand in_scope acc
fvsOfRowSigs [] fv_cand in_scope acc = emptyFV fv_cand in_scope acc

fvsOfRowSig :: RowSig p -> KiFV p
fvsOfRowSig (RowTySig _ ty) f bound_vars acc = fvsOfType_ClosedTv ty f bound_vars acc
fvsOfRowSig (RowKiSig _ ki) f bound_vars acc = fvsOfMonoKind ki f bound_vars acc

almostDevoidKiCoVarOfKiCo :: KiCoVar p -> KindCoercion p -> Bool
almostDevoidKiCoVarOfKiCo kcv kco = almost_devoid_kico_var_of_kico kco kcv

almost_devoid_kico_var_of_kico :: KindCoercion p -> KiCoVar p  -> Bool
almost_devoid_kico_var_of_kico (Refl {}) _ = True
almost_devoid_kico_var_of_kico BI_U_A _ = True
almost_devoid_kico_var_of_kico BI_A_L _ = True
almost_devoid_kico_var_of_kico (BI_U_LTEQ {}) _ = True
almost_devoid_kico_var_of_kico (BI_LTEQ_L {}) _ = True

almost_devoid_kico_var_of_kico (LiftEq kco) kcv
  = almost_devoid_kico_var_of_kico kco kcv

almost_devoid_kico_var_of_kico (LiftLT kco) kcv
  = almost_devoid_kico_var_of_kico kco kcv

almost_devoid_kico_var_of_kico (FunCo { fco_arg = co1, fco_res = co2 }) kcv
  = almost_devoid_kico_var_of_kico co1 kcv
    && almost_devoid_kico_var_of_kico co2 kcv

almost_devoid_kico_var_of_kico (KiCoVarCo v) kcv = v /= kcv

almost_devoid_kico_var_of_kico (HoleCo h) kcv = TcCoVar (coHoleCoVar h) /= kcv

almost_devoid_kico_var_of_kico (SymCo kco) kcv
  = almost_devoid_kico_var_of_kico kco kcv

almost_devoid_kico_var_of_kico (TransCo co1 co2) kcv
  = almost_devoid_kico_var_of_kico co1 kcv
    && almost_devoid_kico_var_of_kico co2 kcv

almost_devoid_kico_var_of_kico (SelCo _ kco) kcv
  = almost_devoid_kico_var_of_kico kco kcv

{- *********************************************************************
*                                                                      *
                 Should be elsewhere
*                                                                      *
********************************************************************* -}

-- Used for 'fvsOfRowSig':
-- Asserts there are no free tvs or kcvs. 
fvsOfType_ClosedTv :: forall p. Type p -> KiFV p
fvsOfType_ClosedTv @p ty f kis (kaccl, kaccs)
  = case fvsOfType ty f' is' acc' of
      (_, ts, _, kcs, kaccl, kaccs)
        -> assertPpr (isEmptyVarSet ts && isEmptyVarSet kcs)
           (text "fvsOfType_ClosedTv" {-$$ ppr ty $$ ppr ts $$ ppr kcs-})
           (kaccl, kaccs)
  where
    is' = (emptyVarSet, emptyVarSet, kis)
    acc' = ([], emptyVarSet, [], emptyVarSet, kaccl, kaccs)

    f' :: forall a b. E3 a b (KiVar p) -> Bool
    f' (In1 _) = True
    f' (In2 _) = True
    f' (In3 k) = f k
