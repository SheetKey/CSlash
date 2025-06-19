{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module CSlash.Core.Kind.FVs where

-- import {-# SOURCE #-} CSlash.Core.Type.FVs (deep_ty)

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

import Data.Void

{- *********************************************************************
*                                                                      *
          Endo for free variables
*                                                                      *
********************************************************************* -}

runKiCoVars :: Endo (MkVarSet kcv, MkVarSet kv) -> (MkVarSet kcv, MkVarSet kv)
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
   We have a shallow kind folder that is used by the shallow type folder.
   The only difference is that shallow does not look at co_holes.
   This is meaningless for kinds, which, at this time, cannot contain co_holes.
-}

varsOfMonoKiVarEnv :: Uniquable kv => MkVarEnv kv (MonoKind kv) -> MkVarSet kv
varsOfMonoKiVarEnv kis = varsOfMonoKinds (nonDetEltsUFM kis)

varsOfKind :: Uniquable kv => Kind kv -> MkVarSet kv
varsOfKind ki = case runKiCoVars (deep_ki @Void ki) of
  (_, kvs) -> kvs

varsOfKinds
  :: Uniquable kv => [Kind kv] -> MkVarSet kv
varsOfKinds kis = case runKiCoVars (deep_kis @Void kis) of
  (_, kvs) -> kvs

varsOfMonoKind
  :: Uniquable kv => MonoKind kv -> MkVarSet kv
varsOfMonoKind ki = case runKiCoVars (deep_mki @Void ki) of
  (_, kvs) -> kvs

varsOfMonoKinds
  :: Uniquable kv => [MonoKind kv] -> MkVarSet kv
varsOfMonoKinds kis = case runKiCoVars (deep_mkis @Void kis) of
  (_, kvs) -> kvs

varsOfKindCoercion
  :: (Uniquable kv, Uniquable kcv)
  => KindCoercion kcv kv -> (MkVarSet kcv, MkVarSet kv)
varsOfKindCoercion co = runKiCoVars (deep_co co)

varsOfKindCoercions
  :: (Uniquable kv, Uniquable kcv)
  => [KindCoercion kcv kv] -> (MkVarSet kcv, MkVarSet kv)
varsOfKindCoercions cos = runKiCoVars (deep_cos cos)

deep_ki
  :: (Uniquable kcv, Uniquable kv)
  => Kind kv -> Endo (MkVarSet kcv, MkVarSet kv)
deep_ki = fst $ foldKind deepKcvFolder emptyVarSet

deep_kis
  :: (Uniquable kcv, Uniquable kv)
  => [Kind kv] -> Endo (MkVarSet kcv, MkVarSet kv)
deep_kis = snd $ foldKind deepKcvFolder emptyVarSet

deep_mki
  :: (Uniquable kcv, Uniquable kv)
  => MonoKind kv -> Endo (MkVarSet kcv, MkVarSet kv)
deep_mki = case foldMonoKiCo deepMKcvFolder emptyVarSet of
             (f, _, _, _) -> f

deep_mkis
  :: (Uniquable kcv, Uniquable kv)
  => [MonoKind kv] -> Endo (MkVarSet kcv, MkVarSet kv)
deep_mkis = case foldMonoKiCo deepMKcvFolder emptyVarSet of
              (_, f, _, _) -> f

deep_co
  :: (Uniquable kcv, Uniquable kv)
  => KindCoercion kcv kv -> Endo (MkVarSet kcv, MkVarSet kv)
deep_co = case foldMonoKiCo deepMKcvFolder emptyVarSet of
            (_, _, f, _) -> f

deep_cos
  :: (Uniquable kcv, Uniquable kv)
  => [KindCoercion kcv kv] -> Endo (MkVarSet kcv, MkVarSet kv)
deep_cos = case foldMonoKiCo deepMKcvFolder emptyVarSet of
             (_, _, _, f) -> f

deepKcvFolder
  :: (Uniquable kcv, Uniquable kv)
  => KiCoFolder kcv kv (MkVarSet kv) (Endo (MkVarSet kcv, MkVarSet kv))
deepKcvFolder = KiCoFolder { kcf_kibinder = do_bndr
                           , kcf_mkcf = deepMKcvFolder }
  where
    do_bndr is kv = extendVarSet is kv

deepMKcvFolder
  :: (Uniquable kcv, Uniquable kv)
  => MKiCoFolder kcv kv (MkVarSet kv) (Endo (MkVarSet kcv, MkVarSet kv))
deepMKcvFolder = MKiCoFolder { mkcf_kivar = do_kivar
                             , mkcf_covar = do_covar
                             , mkcf_hole = do_hole }
  where
    do_kivar is v = Endo do_it
      where
        do_it acc@(kcv_acc, kv_acc)
          | v `elemVarSet` is = acc
          | v `elemVarSet` kv_acc = acc
          | otherwise = (kcv_acc, kv_acc `extendVarSet` v)

    do_covar _ v = Endo do_it
      where
        do_it acc@(kcv_acc, kv_acc)
          | v `elemVarSet` kcv_acc = acc
          | otherwise = (kcv_acc `extendVarSet` v, kv_acc)

    do_hole is hole = do_covar is (coHoleCoVar hole)

shallowMKcvFolder
  :: (Uniquable kcv, Uniquable kv)
  => MKiCoFolder kcv kv (MkVarSet kv) (Endo (MkVarSet kcv, MkVarSet kv))
shallowMKcvFolder = MKiCoFolder { mkcf_kivar = do_kivar
                                , mkcf_covar = do_covar
                                , mkcf_hole = do_hole }
  where
    do_kivar is kv = Endo do_it
      where 
        do_it acc@(kcv_acc, kv_acc)
          | kv `elemVarSet` is = acc
          | kv `elemVarSet` kv_acc = acc
          | otherwise = (kcv_acc, kv_acc `extendVarSet` kv)

    do_covar is kcv = Endo do_it
      where 
        do_it acc@(kcv_acc, kv_acc)
          | kcv `elemVarSet` kcv_acc = acc
          | otherwise = (kcv_acc `extendVarSet` kcv, kv_acc)

    do_hole _ _ = mempty
  
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

anyFreeVarsOfMonoKind :: Uniquable kv => (kv -> Bool) -> MonoKind kv -> Bool
anyFreeVarsOfMonoKind check_kv ki = DM.getAny (f ki)
  where (f, _, _, _) = foldMonoKiCo (mafvFolder (const False) check_kv) emptyVarSet

noFreeVarsOfKind :: Uniquable kv => Kind kv -> Bool
noFreeVarsOfKind ki = not $ DM.getAny (f ki)
  where (f, _) = foldKind (afvFolder (const True)) emptyVarSet

noFreeVarsOfMonoKind :: Uniquable kv => MonoKind kv -> Bool
noFreeVarsOfMonoKind ki = not $ DM.getAny (f ki)
  where (f, _, _, _) = foldMonoKiCo (mafvFolder (const True) (const True)) emptyVarSet

{-# INLINE afvFolder #-}
afvFolder :: Uniquable kv => (kv -> Bool) -> KiCoFolder kcv kv (MkVarSet kv) DM.Any
afvFolder check_kv = KiCoFolder { kcf_kibinder = do_bndr
                                , kcf_mkcf = mafvFolder (const (panic "afvFolder")) check_kv }
  where
    do_bndr is kv = is `extendVarSet` kv

{-# INLINE mafvFolder #-}
mafvFolder
  :: Uniquable kv => (kcv -> Bool) -> (kv -> Bool) -> MKiCoFolder kcv kv (MkVarSet kv) DM.Any
mafvFolder check_kcv check_kv = MKiCoFolder { mkcf_kivar = do_kv
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
