{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeAbstractions #-}

module CSlash.Core.Type.FVs where

import CSlash.Cs.Pass

import {-# SOURCE #-} CSlash.Core.Type
import {-# SOURCE #-} CSlash.Core.Folder
import {-# SOURCE #-} CSlash.Core.Mapper

import Data.Monoid as DM ( Endo(..), Any(..) )
import CSlash.Core.Rep
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs hiding (fvsVarBndr, afvFolder, runCoVars)
import CSlash.Core.TyCon

import CSlash.Types.Var
import CSlash.Types.Unique
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Set

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

runVarsForTy
  :: Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
  -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
{-# INLINE runVarsForTy #-}
runVarsForTy f = appEndo f (emptyVarSet, emptyVarSet, emptyVarSet)

runVarsForKi
  :: HasPass p pass
  => Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
  -> KiVarSet p
{-# INLINE runVarsForKi #-}
runVarsForKi f = case appEndo f (emptyVarSet, emptyVarSet, emptyVarSet) of
  (tvs, kcvs, kvs) -> assertPpr (isEmptyVarSet tvs) (text "runVarsForKi tvs" $$ ppr tvs) $
                      assertPpr (isEmptyVarSet kcvs) (text "runVarsForKi kcvs" $$ ppr kcvs) $
                      kvs

runVarsForKiCo 
  :: HasPass p pass
  => Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
  -> (KiCoVarSet p, KiVarSet p)
{-# INLINE runVarsForKiCo #-}
runVarsForKiCo f = case appEndo f (emptyVarSet, emptyVarSet, emptyVarSet) of
  (tvs, kcvs, kvs) -> assertPpr (isEmptyVarSet tvs) (text "runVarsForKi tvs" $$ ppr tvs) $
                      (kcvs, kvs)

runCoVars
  :: Endo (TyCoVarSet p, KiCoVarSet p)
  -> (TyCoVarSet p, KiCoVarSet p)
{-# INLINE runCoVars #-}
runCoVars f = appEndo f (emptyVarSet, emptyVarSet)

runKiCoVars
  :: HasPass p pass
  => Endo (TyCoVarSet p, KiCoVarSet p)
  -> KiCoVarSet p
{-# INLINE runKiCoVars #-}
runKiCoVars f = case appEndo f (emptyVarSet, emptyVarSet) of
  (tcvs, kcvs) -> assertPpr (isEmptyVarSet tcvs) (text "runKiCoVars tcvs" $$ ppr tcvs) $
                  kcvs

{- *********************************************************************
*                                                                      *
          Deep free variables
*                                                                      *
********************************************************************* -}

varsOfTyVarEnv
  :: HasPass p p' => VarEnv (TyVar p1) (Type p) -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
varsOfTyVarEnv tys = varsOfTypes (nonDetEltsUFM tys)

varsOfMonoKiVarEnv :: HasPass p p' => VarEnv kva (MonoKind p) -> KiVarSet p
varsOfMonoKiVarEnv kis = varsOfMonoKinds (nonDetEltsUFM kis)

varsOfKiCoVarEnv :: HasPass p p' => VarEnv kcva (KindCoercion p) -> (KiCoVarSet p, KiVarSet p)
varsOfKiCoVarEnv cos = varsOfKiCos (nonDetEltsUFM cos)

varsOfType :: HasPass p p' => Type p -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
varsOfType ty = runVarsForTy (deep_ty ty)

varsOfTypes :: HasPass p p' => [Type p] -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
varsOfTypes tys = runVarsForTy (deep_tys tys)

varsOfKind :: HasPass p p' => Kind p -> KiVarSet p
varsOfKind ty = runVarsForKi (deep_ki ty)

varsOfKinds :: HasPass p p' => [Kind p] -> KiVarSet p
varsOfKinds tys = runVarsForKi (deep_kis tys)

varsOfMonoKind :: HasPass p p' => MonoKind p -> KiVarSet p
varsOfMonoKind ty = runVarsForKi (deep_mki ty)

varsOfMonoKinds :: HasPass p p' => [MonoKind p] -> KiVarSet p
varsOfMonoKinds tys = runVarsForKi (deep_mkis tys)

varsOfTyCo :: HasPass p p' => TypeCoercion p -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
varsOfTyCo co = runVarsForTy (deep_tco co)

varsOfKiCo :: HasPass p p' => KindCoercion p -> (KiCoVarSet p, KiVarSet p)
varsOfKiCo co = runVarsForKiCo (deep_kco co)

varsOfKiCos :: HasPass p p' => [KindCoercion p] -> (KiCoVarSet p, KiVarSet p)
varsOfKiCos co = runVarsForKiCo (deep_kcos co)

deep_ty :: HasPass p pass => Type p -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
deep_ty = case foldCore deepFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (f, _, _, _, _, _, _, _, _, _) -> f

deep_tys :: HasPass p pass => [Type p] -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
deep_tys = case foldCore deepFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, f, _, _, _, _, _, _, _, _) -> f

deep_tco :: HasPass p pass => TypeCoercion p -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
deep_tco = case foldCore deepFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, _, f, _, _, _, _, _, _, _) -> f

deep_tcos :: HasPass p pass => [TypeCoercion p] -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
deep_tcos = case foldCore deepFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, _, _, f, _, _, _, _, _, _) -> f

deep_mki :: HasPass p pass => MonoKind p -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
deep_mki = case foldCore deepFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, _, _, _, f, _, _, _, _, _) -> f

deep_mkis :: HasPass p pass => [MonoKind p] -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
deep_mkis = case foldCore deepFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, _, _, _, _, f, _, _, _, _) -> f

deep_ki :: HasPass p pass => Kind p -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
deep_ki = case foldCore deepFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, _, _, _, _, _, f, _, _, _) -> f

deep_kis :: HasPass p pass => [Kind p] -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
deep_kis = case foldCore deepFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, _, _, _, _, _, _, f, _, _) -> f

deep_kco :: HasPass p pass => KindCoercion p -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
deep_kco = case foldCore deepFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, _, _, _, _, _, _, _, f, _) -> f

deep_kcos :: HasPass p pass => [KindCoercion p] -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
deep_kcos = case foldCore deepFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, _, _, _, _, _, _, _, _, f) -> f

deepFvFolder
  :: forall p pass. HasPass p pass
  => CoreFolder p
     (TyVarSet p, KiCoVarSet p, KiVarSet p)
     (Endo (TyVarSet p, KiCoVarSet p, KiVarSet p))
deepFvFolder @p @pass =
  let -- folder
        -- :: forall p' pass'. HasPass p' pass'
        -- => CoreFolder p' (TyVarSet p', KiCoVarSet p', KiVarSet p')
        --    (Endo (TyVarSet p', KiCoVarSet p', KiVarSet p'))
      folder = CoreFolder
  	{ cf_ty_view = noView
 	, cf_fa_kv = \(tvs, kcvs, kvs) kv -> (tvs, kcvs, extendVarSet kvs kv)
  	, cf_fa_kcv = \(tvs, kcvs, kvs) kcv -> (tvs, extendVarSet kcvs kcv, kvs)
  	, cf_fa_tv = \(tvs, kcvs, kvs) tv _ -> (extendVarSet tvs tv, kcvs, kvs)
  	, cf_lam_kv = \(tvs, kcvs, kvs) kv -> (tvs, kcvs, extendVarSet kvs kv)
  	, cf_lam_tv = \(tvs, kcvs, kvs) tv -> (extendVarSet tvs tv, kcvs, kvs)
  	, cf_kv = \(_, _, is) kv ->
            let do_it acc@(tvs, kcvs, kvs)
  	          | kv `elemVarSet` is = acc
  	          | kv `elemVarSet` kvs = acc
  	          | otherwise = (tvs, kcvs, extendVarSet kvs kv)
            in Endo do_it
  	, cf_kcv = \(_, is, _) kcv ->
            let do_it acc@(tvs, kcvs, kvs)
  	          | kcv `elemVarSet` is = acc
  	          | kcv `elemVarSet` kcvs = acc
  	          | otherwise
                  = appEndo (deep_mki (varKind kcv))
                    (tvs, extendVarSet kcvs kcv, kvs)
            in Endo do_it
  	, cf_tv = \(is, _, _) tv ->
            let do_it acc@(tvs, kcvs, kvs)
  	          | tv `elemVarSet` is = acc
  	          | tv `elemVarSet` tvs = acc
  	          | otherwise
                  = appEndo (deep_mki (varKind tv))
                    (extendVarSet tvs tv, kcvs, kvs)
            in Endo do_it
  	, cf_tcv = panic "deepFvFolder cf_tcv"
  	, cf_thole = panic "deepFvFolder cf_thole"
  	, cf_khole = \is hole -> case csPass @pass of
  	    Tc -> cf_kcv folder is (TcCoVar $ coHoleCoVar hole)
            _ -> panic "deepFvFolder cf_khole unreachable"
  	}
  in folder

{- *********************************************************************
*                                                                      *
          Shallow free variables
*                                                                      *
********************************************************************* -}

shallowVarsOfTypes :: HasPass p pass => [Type p] -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
shallowVarsOfTypes tys = runVarsForTy (shallow_tys tys)

shallowVarsOfTyVarEnv
  :: HasPass p pass => VarEnv (TyVar p') (Type p) -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
shallowVarsOfTyVarEnv tys = shallowVarsOfTypes (nonDetEltsUFM tys)

shallow_ty :: HasPass p pass => Type p -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
shallow_ty = case foldCore shallowFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (f, _, _, _, _, _, _, _, _, _) -> f

shallow_tys :: HasPass p pass => [Type p] -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
shallow_tys = case foldCore shallowFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, f, _, _, _, _, _, _, _, _) -> f

shallow_tco :: HasPass p pass => TypeCoercion p -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
shallow_tco = case foldCore shallowFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, _, f, _, _, _, _, _, _, _) -> f

shallow_tcos :: HasPass p pass => [TypeCoercion p] -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
shallow_tcos = case foldCore shallowFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, _, _, f, _, _, _, _, _, _) -> f

shallow_mki :: HasPass p pass => MonoKind p -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
shallow_mki = case foldCore shallowFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, _, _, _, f, _, _, _, _, _) -> f

shallow_mkis :: HasPass p pass => [MonoKind p] -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
shallow_mkis = case foldCore shallowFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, _, _, _, _, f, _, _, _, _) -> f

shallow_ki :: HasPass p pass => Kind p -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
shallow_ki = case foldCore shallowFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, _, _, _, _, _, f, _, _, _) -> f

shallow_kis :: HasPass p pass => [Kind p] -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
shallow_kis = case foldCore shallowFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, _, _, _, _, _, _, f, _, _) -> f

shallow_kco :: HasPass p pass => KindCoercion p -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
shallow_kco = case foldCore shallowFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, _, _, _, _, _, _, _, f, _) -> f

shallow_kcos :: HasPass p pass => [KindCoercion p] -> Endo (TyVarSet p, KiCoVarSet p, KiVarSet p)
shallow_kcos = case foldCore shallowFvFolder (emptyVarSet, emptyVarSet, emptyVarSet) of
  (_, _, _, _, _, _, _, _, _, f) -> f

shallowFvFolder
  :: forall p pass. HasPass p pass
  => CoreFolder p
     (TyVarSet p, KiCoVarSet p, KiVarSet p)
     (Endo (TyVarSet p, KiCoVarSet p, KiVarSet p))
shallowFvFolder @p @pass =
  let folder
        :: CoreFolder p
           (TyVarSet p, KiCoVarSet p, KiVarSet p)
           (Endo (TyVarSet p, KiCoVarSet p, KiVarSet p))
      folder = CoreFolder
  	{ cf_ty_view = noView
  	, cf_fa_kv = \(tvs, kcvs, kvs) kv -> (tvs, kcvs, extendVarSet kvs kv)
  	, cf_fa_kcv = \(tvs, kcvs, kvs) kcv -> (tvs, extendVarSet kcvs kcv, kvs)
  	, cf_fa_tv = \(tvs, kcvs, kvs) tv _ -> (extendVarSet tvs tv, kcvs, kvs)
  	, cf_lam_kv = \(tvs, kcvs, kvs) kv -> (tvs, kcvs, extendVarSet kvs kv)
  	, cf_lam_tv = \(tvs, kcvs, kvs) tv -> (extendVarSet tvs tv, kcvs, kvs)
  	, cf_kv = \(_, _, is) kv ->
            let do_it acc@(tvs, kcvs, kvs)
  	          | kv `elemVarSet` is = acc
  	          | kv `elemVarSet` kvs = acc
  	          | otherwise = (tvs, kcvs, extendVarSet kvs kv)
            in Endo do_it
  	, cf_kcv = \(_, is, _) kcv ->
            let do_it acc@(tvs, kcvs, kvs)
  	          | kcv `elemVarSet` is = acc
  	          | kcv `elemVarSet` kcvs = acc
  	          | otherwise
                  = (tvs, extendVarSet kcvs kcv, kvs)
            in Endo do_it
  	, cf_tv = \(is, _, _) tv ->
            let do_it acc@(tvs, kcvs, kvs)
  	          | tv `elemVarSet` is = acc
  	          | tv `elemVarSet` tvs = acc
  	          | otherwise
                  = (extendVarSet tvs tv, kcvs, kvs)
            in Endo do_it
  	, cf_tcv = panic "shallowFvFolder cf_tcv"
  	, cf_thole = panic "shallowFvFolder cf_thole"
  	, cf_khole = \is hole -> case csPass @pass of
  	    Tc -> cf_kcv folder is (TcCoVar $ coHoleCoVar hole)
            _ -> panic "shallowFvFolder cf_khole unreachable"
  	}
  in folder

{- *********************************************************************
*                                                                      *
          Free coercion variables
*                                                                      *
********************************************************************* -}

coVarsOfType :: HasPass p p' => Type p -> (TyCoVarSet p, KiCoVarSet p)
coVarsOfTypes :: HasPass p p' => [Type p] -> (TyCoVarSet p, KiCoVarSet p)
coVarsOfTyCo :: HasPass p p' => TypeCoercion p -> (TyCoVarSet p, KiCoVarSet p)
coVarsOfTyCos :: HasPass p p' => [TypeCoercion p] -> (TyCoVarSet p, KiCoVarSet p)
coVarsOfMonoKind :: HasPass p p' => MonoKind p -> (TyCoVarSet p, KiCoVarSet p)
coVarsOfMonoKinds :: HasPass p p' => [MonoKind p] -> (TyCoVarSet p, KiCoVarSet p)
coVarsOfKind :: HasPass p p' => Kind p -> (TyCoVarSet p, KiCoVarSet p)
coVarsOfKinds :: HasPass p p' => [Kind p] -> (TyCoVarSet p, KiCoVarSet p)
coVarsOfKiCo :: HasPass p p' => KindCoercion p -> KiCoVarSet p
coVarsOfKiCos :: HasPass p p' => [KindCoercion p] -> KiCoVarSet p

coVarsOfType ty = runCoVars (deep_cv_ty ty)
coVarsOfTypes tys = runCoVars (deep_cv_tys tys)
coVarsOfTyCo co = runCoVars (deep_cv_tco co)
coVarsOfTyCos cos = runCoVars (deep_cv_tcos cos)
coVarsOfMonoKind ty = runCoVars (deep_cv_mki ty)
coVarsOfMonoKinds tys = runCoVars (deep_cv_mkis tys)
coVarsOfKind ty = runCoVars (deep_cv_ki ty)
coVarsOfKinds tys = runCoVars (deep_cv_kis tys)
coVarsOfKiCo co = runKiCoVars (deep_cv_kco co)
coVarsOfKiCos cos = runKiCoVars (deep_cv_kcos cos)

deep_cv_ty :: HasPass p p' => Type p -> Endo (TyCoVarSet p, KiCoVarSet p)
deep_cv_ty = case foldCore deepCoVarFolder (emptyVarSet, emptyVarSet) of
  (f, _, _, _, _, _, _, _, _, _) -> f

deep_cv_tys :: HasPass p p' => [Type p] -> Endo (TyCoVarSet p, KiCoVarSet p)
deep_cv_tys = case foldCore deepCoVarFolder (emptyVarSet, emptyVarSet) of
  (_, f, _, _, _, _, _, _, _, _) -> f

deep_cv_tco :: HasPass p p' => TypeCoercion p -> Endo (TyCoVarSet p, KiCoVarSet p)
deep_cv_tco = case foldCore deepCoVarFolder (emptyVarSet, emptyVarSet) of
  (_, _, f, _, _, _, _, _, _, _) -> f

deep_cv_tcos :: HasPass p p' => [TypeCoercion p] -> Endo (TyCoVarSet p, KiCoVarSet p)
deep_cv_tcos = case foldCore deepCoVarFolder (emptyVarSet, emptyVarSet) of
  (_, _, _, f, _, _, _, _, _, _) -> f

deep_cv_mki :: HasPass p p' => MonoKind p -> Endo (TyCoVarSet p, KiCoVarSet p)
deep_cv_mki = case foldCore deepCoVarFolder (emptyVarSet, emptyVarSet) of
  (_, _, _, _, f, _, _, _, _, _) -> f

deep_cv_mkis :: HasPass p p' => [MonoKind p] -> Endo (TyCoVarSet p, KiCoVarSet p)
deep_cv_mkis = case foldCore deepCoVarFolder (emptyVarSet, emptyVarSet) of
  (_, _, _, _, _, f, _, _, _, _) -> f

deep_cv_ki :: HasPass p p' => Kind p -> Endo (TyCoVarSet p, KiCoVarSet p)
deep_cv_ki = case foldCore deepCoVarFolder (emptyVarSet, emptyVarSet) of
  (_, _, _, _, _, _, f, _, _, _) -> f

deep_cv_kis :: HasPass p p' => [Kind p] -> Endo (TyCoVarSet p, KiCoVarSet p)
deep_cv_kis = case foldCore deepCoVarFolder (emptyVarSet, emptyVarSet) of
  (_, _, _, _, _, _, _, f, _, _) -> f

deep_cv_kco :: HasPass p p' => KindCoercion p -> Endo (TyCoVarSet p, KiCoVarSet p)
deep_cv_kco = case foldCore deepCoVarFolder (emptyVarSet, emptyVarSet) of
  (_, _, _, _, _, _, _, _, f, _) -> f

deep_cv_kcos :: HasPass p p' => [KindCoercion p] -> Endo (TyCoVarSet p, KiCoVarSet p)
deep_cv_kcos = case foldCore deepCoVarFolder (emptyVarSet, emptyVarSet) of
  (_, _, _, _, _, _, _, _, _, f) -> f

deepCoVarFolder
  :: forall p pass. HasPass p pass
  => CoreFolder p
     (TyCoVarSet p, KiCoVarSet p)
     (Endo (TyCoVarSet p, KiCoVarSet p))
deepCoVarFolder @p @pass =
  let folder = CoreFolder
        { cf_ty_view = noView
        , cf_tv = \_ _ -> mempty
        , cf_kv = \_ _ -> mempty
        , cf_tcv = \(is, _) v ->
            let do_it acc@(tacc, kacc) | v `elemVarSet` is = acc
                                       | v `elemVarSet` tacc = acc
                                       | otherwise = appEndo (deep_cv_ty @p @pass (varType v))
                                                     (tacc `extendVarSet` v, kacc)
            in Endo do_it
        , cf_kcv = \(_, is) v ->
            let do_it acc@(tacc, kacc) | v `elemVarSet` is = acc
                                       | v `elemVarSet` kacc = acc
                                       | otherwise = appEndo (deep_cv_mki @p @pass (varKind v))
                                                     (tacc, kacc `extendVarSet` v)
            in Endo do_it
        , cf_thole = \is hole -> case csPass @pass of
            Tc -> cf_tcv folder is (TcCoVar $ tyCoHoleCoVar hole)
            _ -> panic "unreachable"
        , cf_khole = \is hole -> case csPass @pass of
            Tc -> cf_kcv folder is (TcCoVar $ coHoleCoVar hole)
            _ -> panic "unreachable"
        , cf_fa_kv = \is _ -> is
        , cf_fa_tv = \is _ _ -> is
        , cf_lam_kv = \is _ -> is
        , cf_lam_tv = \is _ -> is
        , cf_fa_kcv = \(tacc, kacc) k -> (tacc, extendVarSet kacc k)
        }
  in folder

{- *********************************************************************
*                                                                      *
          The FV versions return deterministic results
*                                                                      *
********************************************************************* -}

-- unionTyKiFV :: TyFV tv kv -> KiFV kv -> TyFV tv kv
-- unionTyKiFV tyfv kifv f is@(_, bks) (tl, ts, kl, ks)
--   = case kifv (f . Right) bks $! (kl, ks) of
--       (kl, ks) -> tyfv f is $! (tl, ts, kl, ks)

type TyFV p = FV (Type p)

liftKiFV :: KiFV p -> TyFV p
liftKiFV kfv f (_, _, kis) (taccl, taccs, kcaccl, kcaccs, kaccl, kaccs)
  = case kfv (f . In3) kis (kaccl, kaccs) of
      (kaccl, kaccs) -> (taccl, taccs, kcaccl, kcaccs, kaccl, kaccs)

fvsOfType :: Type p -> TyFV p

fvsOfType (TyVarTy v) f (bound_vars, bkcs, bks) acc@(acc_list, acc_set, kcl, kcs, kl, ks)
  | not (f (In1 v)) = acc
  | v `elemVarSet` bound_vars = acc
  | v `elemVarSet` acc_set = acc
  | otherwise = liftKiFV (fvsOfMonoKind (varKind v)) f (bound_vars, bkcs, bks)
                (v:acc_list, extendVarSet acc_set v, kcl, kcs, kl, ks)

fvsOfType (TyConApp _ tys) f bound_vars acc = fvsOfTypes tys f bound_vars acc

fvsOfType (AppTy fun arg) f bound_vars acc
  = (fvsOfType fun `unionFV` fvsOfType arg) f bound_vars acc

fvsOfType (FunTy k arg res) f bound_vars acc
  = (liftKiFV (fvsOfMonoKind k) `unionFV` fvsOfType arg `unionFV` fvsOfType res)
    f bound_vars acc

fvsOfType (ForAllTy bndr ty) f bound_vars acc
  = fvsBndr bndr (fvsOfType ty) f bound_vars acc

fvsOfType (ForAllKiCo kcv ty) f bound_vars acc
  = fvsKiCoVarBndr kcv (fvsOfType ty) f bound_vars acc

fvsOfType (TyLamTy v ty) f bound_vars acc
  = fvsVarBndr v (fvsOfType ty) f bound_vars acc

fvsOfType (BigTyLamTy kv ty) f bound_vars acc
  = delFV (In3 kv) (fvsOfType ty) f bound_vars acc

fvsOfType (CastTy ty kco) f bound_vars acc
  = (fvsOfType ty `unionFV` fvsOfKiCo kco) f bound_vars acc

fvsOfType (KindCoercion kco) f bound_vars acc = fvsOfKiCo kco f bound_vars acc

fvsOfType (Embed ki) f bound_vars acc = liftKiFV (fvsOfMonoKind ki) f bound_vars acc

fvsOfKiCo :: KindCoercion p -> TyFV p
fvsOfKiCo (Refl ki) f bound_vars acc = liftKiFV (fvsOfMonoKind ki) f bound_vars acc
fvsOfKiCo BI_U_A f bound_vars acc = acc
fvsOfKiCo BI_A_L f bound_vars acc = acc
fvsOfKiCo (BI_U_LTEQ ki) f bound_vars acc = liftKiFV (fvsOfMonoKind ki) f bound_vars acc
fvsOfKiCo (BI_LTEQ_L ki) f bound_vars acc = liftKiFV (fvsOfMonoKind ki) f bound_vars acc
fvsOfKiCo (LiftEq co) f bound_vars acc = fvsOfKiCo co f bound_vars acc
fvsOfKiCo (LiftLT co) f bound_vars acc = fvsOfKiCo co f bound_vars acc
fvsOfKiCo (FunCo { fco_arg = co1, fco_res = co2 }) f bound_vars acc
  = (fvsOfKiCo co1 `unionFV` fvsOfKiCo co2) f bound_vars acc
fvsOfKiCo (KiCoVarCo kcv) f bound_vars acc = fvsOfKiCoVar kcv f bound_vars acc
fvsOfKiCo (HoleCo h) f bound_vars acc = fvsOfKiCoVar (TcCoVar $ coHoleCoVar h) f bound_vars acc
fvsOfKiCo (SymCo co) f bound_vars acc = fvsOfKiCo co f bound_vars acc
fvsOfKiCo (TransCo co1 co2) f bound_vars acc
  = (fvsOfKiCo co1 `unionFV` fvsOfKiCo co2) f bound_vars acc
fvsOfKiCo (SelCo _ co) f bound_vars acc = fvsOfKiCo co f bound_vars acc

fvsOfKiCoVar :: KiCoVar p -> TyFV p
fvsOfKiCoVar v f (bts, bound_vars, bks) acc@(tl, ts, acc_list, acc_set, kl, ks)
  | not (f (In2 v)) = acc
  | v `elemVarSet` bound_vars = acc
  | v `elemVarSet` acc_set = acc
  | otherwise = liftKiFV (fvsOfMonoKind (varKind v))
                f (bts, bound_vars, bks) (tl, ts, v:acc_list, extendVarSet acc_set v, kl, ks)

fvsOfKiCos :: [KindCoercion p] -> TyFV p
fvsOfKiCos [] f bound_vars acc = emptyFV f bound_vars acc
fvsOfKiCos (co:cos) f bound_vars acc = (fvsOfKiCo co `unionFV` fvsOfKiCos cos) f bound_vars acc

fvsBndr :: ForAllBinder (TyVar p) -> TyFV p -> TyFV p
fvsBndr (Bndr tv _) fvs = fvsVarBndr tv fvs

fvsVarBndrs :: [TyVar p] -> TyFV p -> TyFV p
fvsVarBndrs vars fvs = foldr fvsVarBndr fvs vars

fvsVarBndr :: TyVar p -> TyFV p -> TyFV p
fvsVarBndr var fvs = liftKiFV (fvsOfMonoKind (varKind var)) `unionFV` delFV (In1 var) fvs

fvsTyKiCoVarBndrs :: [Either (TyVar p) (KiCoVar p)] -> TyFV p -> TyFV p
fvsTyKiCoVarBndrs vars fvs = foldr (either fvsVarBndr fvsKiCoVarBndr) fvs vars

fvsKiCoVarBndrs :: [KiCoVar p] -> TyFV p -> TyFV p
fvsKiCoVarBndrs vars fvs = foldr fvsKiCoVarBndr fvs vars

fvsKiCoVarBndr :: KiCoVar p -> TyFV p -> TyFV p
fvsKiCoVarBndr var fvs = liftKiFV (fvsOfMonoKind (varKind var)) `unionFV` delFV (In2 var) fvs

fvsKiVarBndrs :: [KiVar p] -> TyFV p -> TyFV p
fvsKiVarBndrs vars fvs = foldr fvsKiVarBndr fvs vars

fvsKiVarBndr :: KiVar p -> TyFV p -> TyFV p
fvsKiVarBndr var fvs = delFV (In3 var) fvs

fvsOfTypes :: [Type p] -> TyFV p
fvsOfTypes [] fv_cand in_scope acc = emptyFV fv_cand in_scope acc
fvsOfTypes (ty:tys) fv_cand in_scope acc
  = (fvsOfType ty `unionFV` fvsOfTypes tys) fv_cand in_scope acc

varsOfTypeDSet :: Type p -> (DTyVarSet p, DKiCoVarSet p, DKiVarSet p)
varsOfTypeDSet ty = case fvVarAcc (fvsOfType ty) of
  (tvs, _, kcvs, _, kvs, _) -> (mkDVarSet tvs, mkDVarSet kcvs, mkDVarSet kvs)

varsOfTypeList :: Type p -> ([TyVar p], [KiCoVar p], [KiVar p])
varsOfTypeList ty = case fvVarAcc (fvsOfType ty) of
  (tvs, _, kcvs, _, kvs, _) -> (tvs, kcvs, kvs)

varsOfTypesList :: [Type p] -> ([TyVar p], [KiCoVar p], [KiVar p])
varsOfTypesList tys = case fvVarAcc (fvsOfTypes tys) of
  (tvs, _, kcvs, _, kvs, _) -> (tvs, kcvs, kvs)

typeSomeFreeVars
  :: (E3 (TyVar p) (KiCoVar p) (KiVar p) -> Bool)
  -> Type p
  -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
typeSomeFreeVars fv_cand ty = case fvVarAcc (filterFV fv_cand $ fvsOfType ty) of
  (_, tvs, _, kcvs, _, kvs) -> (tvs, kcvs, kvs)

almostDevoidKiCoVarOfTyCo :: KiCoVar p -> TypeCoercion p -> Bool
almostDevoidKiCoVarOfTyCo kcv co = almost_devoid_kico_var_of_tyco co kcv

almost_devoid_kico_var_of_tycos :: [TypeCoercion p] -> KiCoVar p -> Bool
almost_devoid_kico_var_of_tycos [] _ = True
almost_devoid_kico_var_of_tycos (co:cos) kcv
  = almost_devoid_kico_var_of_tyco co kcv
    && almost_devoid_kico_var_of_tycos cos kcv

almost_devoid_kico_var_of_tyco :: TypeCoercion p -> KiCoVar p -> Bool
almost_devoid_kico_var_of_tyco (TyRefl {}) _ = True
almost_devoid_kico_var_of_tyco (GRefl {}) _ = True

almost_devoid_kico_var_of_tyco (TyConAppCo _ cos) kcv = almost_devoid_kico_var_of_tycos cos kcv

almost_devoid_kico_var_of_tyco (AppCo co arg) kcv
  = almost_devoid_kico_var_of_tyco co kcv
    && almost_devoid_kico_var_of_tyco arg kcv

almost_devoid_kico_var_of_tyco
  (ForAllCo { tfco_tv = v, tfco_tv_kind_co = kind_co, tfco_body = co }) kcv
  = almost_devoid_kico_var_of_kico kind_co kcv
    && almost_devoid_kico_var_of_tyco co kcv

almost_devoid_kico_var_of_tyco
  (ForAllCoCo { tfcoco_kcv = v, tfcoco_kcv_kind_co = kind_co, tfcoco_body = co }) kcv
  = almost_devoid_kico_var_of_kico kind_co kcv
    && (v == kcv || almost_devoid_kico_var_of_tyco co kcv)

almost_devoid_kico_var_of_tyco (TyFunCo { tfco_ki = kco, tfco_arg = co1, tfco_res = co2 }) kcv
  = almost_devoid_kico_var_of_kico kco kcv
    && almost_devoid_kico_var_of_tyco co1 kcv
    && almost_devoid_kico_var_of_tyco co2 kcv

almost_devoid_kico_var_of_tyco (TyCoVarCo {}) _ = True

almost_devoid_kico_var_of_tyco (TyHoleCo {}) _ = True

almost_devoid_kico_var_of_tyco (TySymCo co) kcv
  = almost_devoid_kico_var_of_tyco co kcv

almost_devoid_kico_var_of_tyco (TyTransCo co1 co2) kcv
  = almost_devoid_kico_var_of_tyco co1 kcv
    && almost_devoid_kico_var_of_tyco co2 kcv

almost_devoid_kico_var_of_tyco (LRCo _ co) kcv
  = almost_devoid_kico_var_of_tyco co kcv

almost_devoid_kico_var_of_tyco (LiftKCo kco) kcv
  = almost_devoid_kico_var_of_kico kco kcv

{- *********************************************************************
*                                                                      *
            Injective free vars
*                                                                      *
********************************************************************* -}

isInjectiveInType :: HasPass p pass => TyVar p -> Type p -> Bool
isInjectiveInType tv ty = go ty
  where
    go ty | Just ty' <- rewriterView ty = go ty'
    go (TyVarTy tv') = tv' == tv
    go (AppTy f a) = go f || go a
    go (FunTy _ ty1 ty2) = go ty1 || go ty2
    go (TyConApp tc tys) = go_tc tc tys
    go (ForAllTy (Bndr tv' _) ty) = tv /= tv' && go ty
    go (ForAllKiCo _ ty) = go ty
    go (CastTy ty _) = go ty
    go KindCoercion{} = False
    go Embed{} = False
    go (TyLamTy tv' ty) = tv /= tv' && go ty
    go (BigTyLamTy _ ty) = go ty
    

    go_tc tc tys = any go tys

{- *********************************************************************
*                                                                      *
            Any free vars
*                                                                      *
********************************************************************* -}

anyFreeVarsOfMonoKind
  :: (TyCoVar p -> Bool) -> (TyVar p -> Bool) -> (KiCoVar p -> Bool) -> (KiVar p -> Bool)
  -> MonoKind p -> Bool
anyFreeVarsOfMonoKind tcv tv kcv kv ki = DM.getAny (f ki)
  where (_, _, _, _, f, _, _, _, _, _) = foldCore (afvFolder tcv tv kcv kv)
                          (emptyVarSet, emptyVarSet, emptyVarSet, emptyVarSet)

noFreeVarsOfType :: Type p -> Bool
noFreeVarsOfType ty = not $ DM.getAny (f ty)
  where (f, _, _, _, _, _, _, _, _, _) = foldCore
          (afvFolder (const True) (const True) (const True) (const True))
          (emptyVarSet, emptyVarSet, emptyVarSet, emptyVarSet)

noFreeVarsOfMonoKind :: MonoKind p -> Bool
noFreeVarsOfMonoKind ki = not $ DM.getAny (f ki)
  where (_, _, _, _, f, _, _, _, _, _) = foldCore
          (afvFolder (const True) (const True) (const True) (const True))
          (emptyVarSet, emptyVarSet, emptyVarSet, emptyVarSet)

afvFolder
  :: (TyCoVar p -> Bool) -> (TyVar p -> Bool) -> (KiCoVar p -> Bool) -> (KiVar p -> Bool)
  -> CoreFolder p
     (TyCoVarSet p, TyVarSet p, KiCoVarSet p, KiVarSet p)
     DM.Any
afvFolder f_tcv f_tv f_kcv f_kv = CoreFolder
  { cf_ty_view = noView
  , cf_tv = \(_, is, _, _) v -> Any (not (v `elemVarSet` is) && f_tv v)
  , cf_tcv = \(is, _, _, _) v -> Any (not (v `elemVarSet` is) && f_tcv v)
  , cf_kv = \(_, _, _, is) v -> Any (not (v `elemVarSet` is) && f_kv v)
  , cf_kcv = \(_, _, is, _) v -> Any (not (v `elemVarSet` is) && f_kcv v)
  , cf_khole = panic "do_hole"
  , cf_thole = panic "do_hole"
  , cf_fa_kv = \(tcvs, tvs, kcvs, kvs) v -> (tcvs, tvs, kcvs, extendVarSet kvs v)
  , cf_fa_kcv = \(tcvs, tvs, kcvs, kvs) v -> (tcvs, tvs, extendVarSet kcvs v, kvs)
  , cf_fa_tv = \(tcvs, tvs, kcvs, kvs) v _ -> (tcvs, extendVarSet tvs v, kcvs, kvs)
  , cf_lam_kv = \(tcvs, tvs, kcvs, kvs) v -> (tcvs, tvs, kcvs, extendVarSet kvs v)
  , cf_lam_tv = \(tcvs, tvs, kcvs, kvs) v -> (tcvs, extendVarSet tvs v, kcvs, kvs)
  }

{- *********************************************************************
*                                                                      *
            Free type constructors
*                                                                      *
********************************************************************* -}

tyConsOfType :: HasPass p pass => Type p -> UniqSet (TyCon p)
tyConsOfType ty = go ty
  where
    -- go :: Type -> UniqSet TyCon
    go ty | Just ty' <- coreView ty = go ty'
    go (TyVarTy {}) = emptyUniqSet
    go (TyConApp tc tys) = go_tc tc `unionUniqSets` tyConsOfTypes tys
    go (AppTy a b) = go a `unionUniqSets` go b
    go (FunTy _ a b) = go a `unionUniqSets` go b
    go (ForAllTy _ ty) = go ty
    go (TyLamTy _ ty) = go ty
    go other = pprPanic "tyConsOfType" (ppr other)

    go_tc tc = unitUniqSet tc

tyConsOfTypes :: HasPass p pass => [Type p] -> UniqSet (TyCon p)
tyConsOfTypes tys = foldr (unionUniqSets . tyConsOfType) emptyUniqSet tys

{- *********************************************************************
*                                                                      *
            Free type constructors
*                                                                      *
********************************************************************* -}

closedKind :: HasPass p pass => Kind p -> Maybe (Kind p)
closedKind = case mapCoreX closedMapper of
  (_, _, _, _, _, _, f, _, _, _) -> f (emptyVarSet, emptyVarSet, emptyVarSet, emptyVarSet)

closedMonoKind :: HasPass p pass => MonoKind p -> Maybe (MonoKind p)
closedMonoKind = case mapCoreX closedMapper of
  (_, _, _, _, f, _, _, _, _, _) -> f (emptyVarSet, emptyVarSet, emptyVarSet, emptyVarSet)

closedMonoKinds :: HasPass p pass => [MonoKind p] -> Maybe [MonoKind p]
closedMonoKinds = case mapCoreX closedMapper of
  (_, _, _, _, _, f, _, _, _, _) -> f (emptyVarSet, emptyVarSet, emptyVarSet, emptyVarSet)

closedKiCo :: HasPass p pass => KindCoercion p -> Maybe (KindCoercion p)
closedKiCo = case mapCoreX closedMapper of
  (_, _, _, _, _, _, _, _, f, _) -> f (emptyVarSet, emptyVarSet, emptyVarSet, emptyVarSet)

closedMapper :: CoreMapper p p (TyCoVarSet p, TyVarSet p, KiCoVarSet p, KiVarSet p) Maybe
closedMapper = CoreMapper
  { cm_kv = \(_, _, _, is) v -> if v `elemVarSet` is then Just (KiVarKi v) else Nothing
  , cm_kcv = \(_, _, is, _) v -> if v `elemVarSet` is then Just (KiCoVarCo v) else Nothing
  , cm_tv = \(_, is, _, _) v -> if v `elemVarSet` is then Just (TyVarTy v) else Nothing
  , cm_tcv = \(is, _, _, _) v -> if v `elemVarSet` is then Just (TyCoVarCo v) else Nothing
  , cm_khole = panic "closedMapper khole"
  , cm_thole = panic "closedMapper thole"
  , cm_lam_kv = \(tcvs, tvs, kcvs, kvs) kv f ->
      let env' = (tcvs, tvs, kcvs, extendVarSet kvs kv)
      in f env' kv
  , cm_lam_tv = \(tcvs, tvs, kcvs, kvs) tv f ->
      let env' = (tcvs, extendVarSet tvs tv, kcvs, kvs)
      in f env' tv
  , cm_fa_kv = \(tcvs, tvs, kcvs, kvs) kv f ->
      let env' = (tcvs, tvs, kcvs, extendVarSet kvs kv)
      in f env' kv
  , cm_fa_kcv = \(tcvs, tvs, kcvs, kvs) kcv f ->
      let env' = (tcvs, tvs, extendVarSet kcvs kcv, kvs)
      in f env' kcv
  , cm_fa_tv = \(tcvs, tvs, kcvs, kvs) tv _ f ->
      let env' = (tcvs, extendVarSet tvs tv, kcvs, kvs)
      in f env' tv
  , cm_tycon = panic "closedMapper tycon"
  }
