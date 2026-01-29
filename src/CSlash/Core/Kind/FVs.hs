{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE ExplicitForAll #-}

module CSlash.Core.Kind.FVs where

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

runKiCoVars :: Endo (VarSet kcv, VarSet kv) -> (VarSet kcv, VarSet kv)
{-# INLINE runKiCoVars #-}
runKiCoVars f = appEndo f (emptyVarSet, emptyVarSet)

runCoVars :: Endo (VarSet kcv) -> VarSet kcv
{-# INLINE runCoVars #-}
runCoVars f = appEndo f emptyVarSet

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

varsOfMonoKiVarEnv :: VarEnv kva (MonoKind p) -> KiVarSet p
varsOfMonoKiVarEnv kis = varsOfMonoKinds (nonDetEltsUFM kis)

varsOfKind :: Kind p -> KiVarSet p
varsOfKind ki = case runKiCoVars (deep_ki ki) of
  (_, kvs) -> kvs
  -- maybe this should be 'assert (isEmptyVarSet kcvs)'

varsOfKinds
  :: [Kind p] -> KiVarSet p
varsOfKinds kis = case runKiCoVars (deep_kis kis) of
  (_, kvs) -> kvs

varsOfMonoKind
  :: MonoKind p -> KiVarSet p
varsOfMonoKind ki = case runKiCoVars (deep_mki ki) of
  (_, kvs) -> kvs

varsOfMonoKinds
  :: [MonoKind p] -> KiVarSet p
varsOfMonoKinds kis = case runKiCoVars (deep_mkis kis) of
  (_, kvs) -> kvs

varsOfKindCoercion
  :: KindCoercion p -> (KiCoVarSet p, KiVarSet p)
varsOfKindCoercion co = runKiCoVars (deep_co co)

varsOfKindCoercions
  :: [KindCoercion p] -> (KiCoVarSet p, KiVarSet p)
varsOfKindCoercions cos = runKiCoVars (deep_cos cos)

deep_ki
  :: Kind p -> Endo (KiCoVarSet p, KiVarSet p)
deep_ki = fst $ foldKind deepKcvFolder (emptyVarSet, emptyVarSet)

deep_kis
  :: [Kind p] -> Endo (KiCoVarSet p, KiVarSet p)
deep_kis = snd $ foldKind deepKcvFolder (emptyVarSet, emptyVarSet)

deep_mki
  :: MonoKind p -> Endo (KiCoVarSet p, KiVarSet p)
deep_mki = case foldMonoKiCo deepMKcvFolder (emptyVarSet, emptyVarSet) of
             (f, _, _, _) -> f

deep_mkis
  :: [MonoKind p] -> Endo (KiCoVarSet p, KiVarSet p)
deep_mkis = case foldMonoKiCo deepMKcvFolder (emptyVarSet, emptyVarSet) of
              (_, f, _, _) -> f

deep_co
  :: KindCoercion p -> Endo (KiCoVarSet p, KiVarSet p)
deep_co = case foldMonoKiCo deepMKcvFolder (emptyVarSet, emptyVarSet) of
            (_, _, f, _) -> f

deep_cos
  :: [KindCoercion p] -> Endo (KiCoVarSet p, KiVarSet p)
deep_cos = case foldMonoKiCo deepMKcvFolder (emptyVarSet, emptyVarSet) of
             (_, _, _, f) -> f

deepKcvFolder
  :: KiCoFolder p
     (KiCoVarSet p, KiVarSet p)
     (Endo (KiCoVarSet p, KiVarSet p))
deepKcvFolder = KiCoFolder { kcf_kibinder = do_bndr
                           , kcf_mkcf = deepMKcvFolder }
  where
    do_bndr (kcvis, is) kv = (kcvis, extendVarSet is kv)

deepMKcvFolder
  :: forall p.
     MKiCoFolder p
     (KiCoVarSet p, KiVarSet p)
     (Endo (KiCoVarSet p, KiVarSet p))
deepMKcvFolder @kv = MKiCoFolder { mkcf_kivar = do_kivar
                                 , mkcf_covar = do_covar
                                 , mkcf_hole = do_hole }
  where
    do_kivar
      :: (KiCoVarSet p, KiVarSet p)
      -> KiVar p
      -> Endo (KiCoVarSet p, KiVarSet p)
    do_kivar (_, is) v = Endo do_it
      where
        do_it acc@(kcv_acc, kv_acc)
          | v `elemVarSet` is = acc
          | v `elemVarSet` kv_acc = acc
          | otherwise = (kcv_acc, kv_acc `extendVarSet` v)

    do_covar
      :: (KiCoVarSet p, KiVarSet p)
      -> KiCoVar p
      -> Endo (KiCoVarSet p, KiVarSet p)
    do_covar (is, _) v = Endo do_it
      where
        do_it acc@(kcv_acc, kv_acc)
          | v `elemVarSet` is = acc
          | v `elemVarSet` kcv_acc = acc
          | otherwise = appEndo (deep_mki (varKind v))
                        $ (kcv_acc `extendVarSet` v, kv_acc)

    -- do_hole
    --   :: (VarSet (KiCoVar kv), VarSet kv)
    --   -> KindCoercionHole
    --   -> (Endo (VarSet (KiCoVar kv), VarSet kv))
    do_hole is hole = panic "do_covar is (coHoleCoVar hole)"

shallowMKcvFolder
  :: forall p.
     MKiCoFolder p
     (KiCoVarSet p, KiVarSet p)
     (Endo (KiCoVarSet p, KiVarSet p))
shallowMKcvFolder = MKiCoFolder { mkcf_kivar = do_kivar
                                , mkcf_covar = do_covar
                                , mkcf_hole = do_hole }
  where
    do_kivar (_, is) kv = Endo do_it
      where 
        do_it acc@(kcv_acc, kv_acc)
          | kv `elemVarSet` is = acc
          | kv `elemVarSet` kv_acc = acc
          | otherwise = (kcv_acc, kv_acc `extendVarSet` kv)

    do_covar (is, _) kcv = Endo do_it
      where 
        do_it acc@(kcv_acc, kv_acc)
          | kcv `elemVarSet` is = acc
          | kcv `elemVarSet` kcv_acc = acc
          | otherwise = (kcv_acc `extendVarSet` kcv, kv_acc)

    do_hole _ _ = mempty
  
{- *********************************************************************
*                                                                      *
          Free coercion variables
*                                                                      *
********************************************************************* -}

coVarsOfKiCo :: KindCoercion p -> KiCoVarSet p
coVarsOfKiCo co = runCoVars (deep_kcv_co co)

deep_kcv_mki :: MonoKind p -> Endo (KiCoVarSet p)
deep_kcv_mki = case foldMonoKiCo deepKiCoVarFolder emptyVarSet of
  (f, _, _, _) -> f

deep_kcv_mkis :: [MonoKind p] -> Endo (KiCoVarSet p)
deep_kcv_mkis = case foldMonoKiCo deepKiCoVarFolder emptyVarSet of
  (_, f, _, _) -> f

deep_kcv_co :: KindCoercion p -> Endo (KiCoVarSet p)
deep_kcv_co = case foldMonoKiCo deepKiCoVarFolder emptyVarSet of
  (_, _, f, _) -> f

deep_kcv_cos :: [KindCoercion p] -> Endo (KiCoVarSet p)
deep_kcv_cos = case foldMonoKiCo deepKiCoVarFolder emptyVarSet of
  (_, _, _, f) -> f

deepKiCoVarFolder :: MKiCoFolder p (KiCoVarSet p) (Endo (KiCoVarSet p))
deepKiCoVarFolder = MKiCoFolder { mkcf_kivar = do_kivar
                                , mkcf_covar = do_covar
                                , mkcf_hole = do_hole }
  where
    do_kivar _ _ = mempty

    do_covar is v = Endo do_it
      where
        do_it acc | v `elemVarSet` is = acc
                  | v `elemVarSet` acc = acc
                  | otherwise = acc `extendVarSet` v

    do_hole is hole = panic "do_covar is (coHoleCoVar hole)"

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
fvsOfMonoKind (BIKi{}) f found_vars acc = acc
fvsOfMonoKind (KiPredApp _ k1 k2) f bound_vars acc
  = (fvsOfMonoKind k1 `unionFV` fvsOfMonoKind k2) f bound_vars acc
fvsOfMonoKind (FunKi _ arg res) f bound_var acc
  = (fvsOfMonoKind arg `unionFV` fvsOfMonoKind res) f bound_var acc

fvsOfMonoKinds :: [MonoKind p] -> KiFV p
fvsOfMonoKinds (ki:kis) fv_cand in_scope acc
  = (fvsOfMonoKind ki `unionFV` fvsOfMonoKinds kis) fv_cand in_scope acc
fvsOfMonoKinds [] fv_cand in_scope acc = emptyFV fv_cand in_scope acc

{- *********************************************************************
*                                                                      *
                 Any free vars
*                                                                      *
********************************************************************* -}

anyFreeVarsOfKind :: (KiVar p -> Bool) -> Kind p -> Bool
anyFreeVarsOfKind check_fv ki = DM.getAny (f ki)
  where (f, _) = foldKind (afvFolder check_fv) (emptyVarSet, emptyVarSet)

anyFreeVarsOfMonoKind :: (KiVar p -> Bool) -> MonoKind p -> Bool
anyFreeVarsOfMonoKind check_kv ki = DM.getAny (f ki)
  where (f, _, _, _) = foldMonoKiCo (mafvFolder (const False) check_kv)
                       (emptyVarSet, emptyVarSet)

noFreeVarsOfKind :: Kind p -> Bool
noFreeVarsOfKind ki = not $ DM.getAny (f ki)
  where (f, _) = foldKind (afvFolder (const True)) (emptyVarSet, emptyVarSet)

noFreeVarsOfMonoKind :: MonoKind p -> Bool
noFreeVarsOfMonoKind ki = not $ DM.getAny (f ki)
  where (f, _, _, _) = foldMonoKiCo (mafvFolder (const True) (const True))
                       (emptyVarSet, emptyVarSet)

{-# INLINE afvFolder #-}
afvFolder
  :: (KiVar p -> Bool)
  -> KiCoFolder p (KiCoVarSet p, KiVarSet p) DM.Any
afvFolder check_kv = KiCoFolder { kcf_kibinder = do_bndr
                                , kcf_mkcf = mafvFolder (const (panic "afvFolder")) check_kv }
  where
    do_bndr (kcv, is) kv = (kcv, is `extendVarSet` kv)

{-# INLINE mafvFolder #-}
mafvFolder
  :: (KiCoVar p -> Bool) -> (KiVar p -> Bool)
  -> MKiCoFolder p (KiCoVarSet p, KiVarSet p) DM.Any
mafvFolder check_kcv check_kv = MKiCoFolder { mkcf_kivar = do_kv
                                            , mkcf_covar = do_kcv
                                            , mkcf_hole = do_hole }
  where
    do_kv (_, is) kv = Any (not (kv `elemVarSet` is) && check_kv kv)
    do_kcv (is, _) kcv = Any (not (kcv `elemVarSet` is) && check_kcv kcv)
    do_hole _ _ = Any False
