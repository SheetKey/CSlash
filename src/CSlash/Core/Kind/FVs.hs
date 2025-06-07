{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE ExplicitForAll #-}

module CSlash.Core.Kind.FVs where

import {-# SOURCE #-} CSlash.Core.Type.FVs (deep_ty)

import Data.Monoid as DM ( Endo(..), Any(..) )
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
          Endo for free variables
*                                                                      *
********************************************************************* -}

runKiCoVars :: Endo (MkVarSet kv, MkVarSet kcv) -> (MkVarSet kv, MkVarSet kcv)
{-# INLINE runKiCoVars #-}
runKiCoVars f = appEndo f (emptyVarSet, emptyVarSet)

{- *********************************************************************
*                                                                      *
          Free variables
*                                                                      *
********************************************************************* -}

{- NOTE: For kinds, we DO NOT have to distinguish between
   deep and shallow variables as in GHC. 
   This is primarily because we do not represent types of kinds (i.e., sorts).

   Additionally, we do not need a separate folder for getting ONLY KiCoVars.
   Moreover, at this time, Kinds cannot contain KiCoVars.

   In summary, "deep" is used for historical reasons and is likely to change.
-}

varsOfKind
  :: forall kv kcv. (Uniquable kv, Uniquable kcv, Outputable kcv)
  => Kind kv -> MkVarSet kv
varsOfKind @_ @kcv ki = case runKiCoVars (deep_ki ki) of
  (kvs, kcvs) -> assertPpr (isEmptyVarSet (kcvs :: MkVarSet kcv))
                 (text "varsOfKind/kcvs" <+> ppr kcvs) kvs

varsOfKinds
  :: forall kv kcv. (Uniquable kv, Uniquable kcv, Outputable kcv)
  => [Kind kv] -> MkVarSet kv
varsOfKinds @_ @kcv kis = case runKiCoVars (deep_kis kis) of
  (kvs, kcvs) -> assertPpr (isEmptyVarSet (kcvs :: MkVarSet kcv))
                 (text "varsOfKinds/kcvs" <+> ppr kcvs) kvs

varsOfMonoKind
  :: forall kv kcv. (Uniquable kv, Uniquable kcv, Outputable kcv)
  => MonoKind kv -> MkVarSet kv
varsOfMonoKind @_ @kcv ki = case runKiCoVars (deep_mki ki) of
  (kvs, kcvs) -> assertPpr (isEmptyVarSet (kcvs :: MkVarSet kcv))
                 (text "varsOfMonoKind/kcvs" <+> ppr kcvs) kvs

varsOfMonoKinds
  :: forall kv kcv. (Uniquable kv, Uniquable kcv, Outputable kcv)
  => [Kind kv] -> MkVarSet kv
varsOfMonoKinds @_ @kcv kis = case runKiCoVars (deep_kis kis) of
  (kvs, kcvs) -> assertPpr (isEmptyVarSet (kcvs :: MkVarSet kcv))
                 (text "varsOfMonoKinds/kcvs" <+> ppr kcvs) kvs

varsOfKindCoercion
  :: (Uniquable kv, Uniquable kcv)
  => KindCoercion kv kcv -> (MkVarSet kv, MkVarSet kcv)
varsOfKindCoercion co = runKiCoVars (deep_co co)

varsOfKindCoercions
  :: (Uniquable kv, Uniquable kcv)
  => [KindCoercion kv kcv] -> (MkVarSet kv, MkVarSet kcv)
varsOfKindCoercions cos = runKiCoVars (deep_cos cos)

deep_ki
  :: (Uniquable kv, Uniquable kcv)
  => Kind kv -> Endo (MkVarSet kv, MkVarSet kcv)
deep_ki = fst $ foldKind deepKcvFolder emptyVarSet

deep_kis
  :: (Uniquable kv, Uniquable kcv)
  => [Kind kv] -> Endo (MkVarSet kv, MkVarSet kcv)
deep_kis = snd $ foldKind deepKcvFolder emptyVarSet

deep_mki
  :: (Uniquable kv, Uniquable kcv)
  => MonoKind kv -> Endo (MkVarSet kv, MkVarSet kcv)
deep_mki = case foldMonoKiCo deepMKcvFolder emptyVarSet of
             (f, _, _, _) -> f

deep_mkis
  :: (Uniquable kv, Uniquable kcv)
  => [MonoKind kv] -> Endo (MkVarSet kv, MkVarSet kcv)
deep_mkis = case foldMonoKiCo deepMKcvFolder emptyVarSet of
              (_, f, _, _) -> f

deep_co
  :: (Uniquable kv, Uniquable kcv)
  => KindCoercion kv kcv -> Endo (MkVarSet kv, MkVarSet kcv)
deep_co = case foldMonoKiCo deepMKcvFolder emptyVarSet of
            (_, _, f, _) -> f

deep_cos
  :: (Uniquable kv, Uniquable kcv)
  => [KindCoercion kv kcv] -> Endo (MkVarSet kv, MkVarSet kcv)
deep_cos = case foldMonoKiCo deepMKcvFolder emptyVarSet of
             (_, _, _, f) -> f

deepKcvFolder
  :: (Uniquable kv, Uniquable kcv)
  => KiCoFolder kv kcv (MkVarSet kv) (Endo (MkVarSet kv, MkVarSet kcv))
deepKcvFolder = KiCoFolder { kcf_kibinder = do_bndr
                           , kcf_mkcf = deepMKcvFolder }
  where
    do_bndr is kv = extendVarSet is kv

deepMKcvFolder
  :: (Uniquable kv, Uniquable kcv)
  => MKiCoFolder kv kcv (MkVarSet kv) (Endo (MkVarSet kv, MkVarSet kcv))
deepMKcvFolder = MKiCoFolder { mkcf_kivar = do_kivar
                             , mkcf_covar = do_covar
                             , mkcf_hole = do_hole }
  where
    do_kivar is v = Endo do_it
      where
        do_it acc@(kv_acc, kcv_acc)
          | v `elemVarSet` is = acc
          | v `elemVarSet` kv_acc = acc
          | otherwise = (kv_acc `extendVarSet` v, kcv_acc)

    do_covar _ v = Endo do_it
      where
        do_it acc@(kv_acc, kcv_acc)
          | v `elemVarSet` kcv_acc = acc
          | otherwise = (kv_acc, kcv_acc `extendVarSet` v)

    do_hole is hole = do_covar is (coHoleCoVar hole)
  
{- *********************************************************************
*                                                                      *
          The FV versions return deterministic results
*                                                                      *
********************************************************************* -}

type KiFV kv = FV (Kind kv)

varsOfKindDSet :: Uniquable kv => Kind kv -> MkDVarSet kv
varsOfKindDSet ki = mkDVarSet $ fst $ fvVarAcc $ fvsOfKind ki

varsOfKindList :: Uniquable kv => Kind kv -> [kv]
varsOfKindList ki = fst $ fvVarAcc $ fvsOfKind ki

varsOfMonoKindDSet :: Uniquable kv => MonoKind kv -> MkDVarSet kv
varsOfMonoKindDSet ki = mkDVarSet $ fst $ fvVarAcc $ fvsOfMonoKind ki

varsOfMonoKindList :: Uniquable kv => MonoKind kv -> [kv]
varsOfMonoKindList ki = fst $ fvVarAcc $ fvsOfMonoKind ki

varsOfMonoKindsList :: Uniquable kv => [MonoKind kv] -> [kv]
varsOfMonoKindsList kis = fst $ fvVarAcc $ fvsOfMonoKinds kis

fvsOfKind :: Uniquable kv => Kind kv -> KiFV kv
fvsOfKind (Mono ki) f bound_vars acc = fvsOfMonoKind ki f bound_vars acc
fvsOfKind (ForAllKi kv ki) f bound_vars acc
  = fvsVarBndr kv (fvsOfKind ki) f bound_vars acc

fvsVarBndr :: Uniquable kv => kv -> KiFV kv -> KiFV kv
fvsVarBndr kv fvs = delFV kv fvs

fvsOfMonoKind :: Uniquable kv => MonoKind kv -> KiFV kv
fvsOfMonoKind (KiVarKi v) f bound_vars (acc_list, acc_set)
  | not (f v) = (acc_list, acc_set)
  | v `elemVarSet` bound_vars = (acc_list, acc_set)
  | v `elemVarSet` acc_set = (acc_list, acc_set)
  | otherwise = (v:acc_list, extendVarSet acc_set v)
fvsOfMonoKind (KiConApp _ kis) f bound_vars acc = fvsOfMonoKinds kis f bound_vars acc
fvsOfMonoKind (FunKi _ arg res) f bound_var acc
  = (fvsOfMonoKind arg `unionFV` fvsOfMonoKind res) f bound_var acc

fvsOfMonoKinds :: Uniquable kv => [MonoKind kv] -> KiFV kv
fvsOfMonoKinds (ki:kis) fv_cand in_scope acc
  = (fvsOfMonoKind ki `unionFV` fvsOfMonoKinds kis) fv_cand in_scope acc
fvsOfMonoKinds [] fv_cand in_scope acc = emptyFV fv_cand in_scope acc

{- *********************************************************************
*                                                                      *
                 Any free vars
*                                                                      *
********************************************************************* -}

anyFreeVarsOfKind :: Uniquable kv => (kv -> Bool) -> Kind kv -> Bool
anyFreeVarsOfKind check_fv ki = DM.getAny (f ki)
  where (f, _) = foldKind (afvFolder check_fv) emptyVarSet

anyFreeVarsOfMonoKind :: Uniquable kv => (kv -> Bool) -> (kcv -> Bool) -> MonoKind kv -> Bool
anyFreeVarsOfMonoKind check_kv check_kcv ki = DM.getAny (f ki)
  where (f, _, _, _) = foldMonoKiCo (mafvFolder check_kv check_kcv) emptyVarSet

noFreeVarsOfKind :: Uniquable kv => Kind kv -> Bool
noFreeVarsOfKind ki = not $ DM.getAny (f ki)
  where (f, _) = foldKind (afvFolder (const True)) emptyVarSet

noFreeVarsOfMonoKind :: Uniquable kv => MonoKind kv -> Bool
noFreeVarsOfMonoKind ki = not $ DM.getAny (f ki)
  where (f, _, _, _) = foldMonoKiCo (mafvFolder (const True) (const True)) emptyVarSet

{-# INLINE afvFolder #-}
afvFolder :: Uniquable kv => (kv -> Bool) -> KiCoFolder kv kcv (MkVarSet kv) DM.Any
afvFolder check_kv = KiCoFolder { kcf_kibinder = do_bndr
                                , kcf_mkcf = mafvFolder check_kv (const (panic "afvFolder")) }
  where
    do_bndr is kv = is `extendVarSet` kv

{-# INLINE mafvFolder #-}
mafvFolder
  :: Uniquable kv => (kv -> Bool) -> (kcv -> Bool) -> MKiCoFolder kv kcv (MkVarSet kv) DM.Any
mafvFolder check_kv check_kcv = MKiCoFolder { mkcf_kivar = do_kv
                                            , mkcf_covar = do_kcv
                                            , mkcf_hole = do_hole }
  where
    do_kv is kv = Any (not (kv `elemVarSet` is) && check_kv kv)
    do_kcv is kcv = Any (check_kcv kcv)
    do_hole _ _ = Any False

{- *********************************************************************
*                                                                      *
                 scopedSort
*                                                                      *
********************************************************************* -}

scopedSort :: [kv] -> [kv]
scopedSort = go []
  where
    go acc [] = reverse acc
    go acc (kv:kvs) = go acc' kvs
      where
        acc' = insert kv acc

    insert kv [] = [kv]
    insert kv (a:as) = (kv:a:as)

varsOfMonoKindsWellScoped :: Uniquable kv => [MonoKind kv] -> [kv]
varsOfMonoKindsWellScoped = scopedSort . varsOfMonoKindsList
