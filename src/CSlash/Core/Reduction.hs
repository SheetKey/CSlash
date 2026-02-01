{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Reduction where

import CSlash.Cs.Pass

-- import GHC.Core.Class      ( Class(classTyCon) )
-- import GHC.Core.Coercion
-- import GHC.Core.Predicate  ( mkClassPred )
import CSlash.Core.TyCon ( TyCon )
import CSlash.Core.Type
import CSlash.Core.Type.Rep
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs
import CSlash.Core.Subst

import CSlash.Data.Pair ( Pair(Pair) )
import CSlash.Data.List.Infinite ( Infinite (..) )
import qualified CSlash.Data.List.Infinite as Inf

import CSlash.Types.Var ( VarBndr(..), PiKiBinder(..), setVarKind )
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set ( TyVarSet, KiVarSet, emptyVarSet )

import CSlash.Utils.Misc ( HasDebugCallStack, equalLength )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Trace

{- *********************************************************************
*                                                                      *
     Reductions
*                                                                      *
********************************************************************* -}

data KiReduction = KiReduction
  { reductionKindCoercion :: KindCoercion Tc
  , reductionReducedKind :: !(MonoKind Tc) }

data TyReduction = TyReduction
  { reductionTypeCoercion :: TypeCoercion Tc
  , reductionReducedType :: !(Type Tc) }

embedKiRedn :: KiReduction -> TyReduction
embedKiRedn (KiReduction kco mki) = mkTyReduction (LiftKCo kco) (Embed mki)

mkTyReduction :: TypeCoercion Tc -> Type Tc -> TyReduction
mkTyReduction co ty = TyReduction co ty
{-# INLINE mkTyReduction #-}

mkKiReduction :: KindCoercion Tc -> MonoKind Tc -> KiReduction
mkKiReduction co ki = KiReduction co ki
{-# INLINE mkKiReduction #-}

data HetTyReduction = HetTyReduction TyReduction (Maybe (KindCoercion Tc))

mkHetTyReduction :: TyReduction -> Maybe (KindCoercion Tc) -> HetTyReduction
mkHetTyReduction = HetTyReduction
{-# INLINE mkHetTyReduction #-}

homogeniseHetTyRedn :: HetTyReduction -> TyReduction
homogeniseHetTyRedn (HetTyReduction redn kco)
  = mkCoherenceRightMRedn redn (mkSymMKiCo kco)
{-# INLINE homogeniseHetTyRedn #-}

instance Outputable TyReduction where
  ppr redn@(TyReduction {}) = braces $ vcat
    [ text "reductionOriginalType:" <+> ppr (reductionOriginalType redn)
    , text "reductionReducedType:" <+> ppr (reductionReducedType redn)
    , text "reductionTypeCoercion:" <+> ppr (reductionTypeCoercion redn)
    ]

instance Outputable KiReduction where
  ppr redn@(KiReduction {}) = braces $ vcat
    [ text "reductionOriginalKind:" <+> ppr (reductionOriginalKind redn)
    , text "reductionReducedKind:" <+> ppr (reductionReducedKind redn)
    , text "reductionKindCoercion:" <+> ppr (reductionKindCoercion redn) ]

reductionOriginalKind :: KiReduction -> MonoKind Tc
reductionOriginalKind = kicoercionLKind . reductionKindCoercion
{-# INLINE reductionOriginalKind #-}

reductionOriginalType :: TyReduction -> Type Tc
reductionOriginalType = tycoercionLType . reductionTypeCoercion
{-# INLINE reductionOriginalType #-}

mkTransRedn :: KindCoercion Tc -> KiReduction -> KiReduction
mkTransRedn co1 redn@(KiReduction co2 _) = redn { reductionKindCoercion = co1 `mkTransKiCo` co2 }
{-# INLINE mkTransRedn #-}

mkTransTyRedn :: TypeCoercion Tc -> TyReduction -> TyReduction
mkTransTyRedn co1 redn@(TyReduction co2 _)
  = redn { reductionTypeCoercion = co1 `mkTyTransCo` co2 }
{-# INLINE mkTransTyRedn #-}

mkReflRednKi :: MonoKind Tc -> KiReduction
mkReflRednKi ki = mkKiReduction (mkReflKiCo ki) ki

mkReflRednTy :: Type Tc -> TyReduction
mkReflRednTy ty = mkTyReduction (mkReflTyCo ty) ty

mkGReflLeftRednTy :: Type Tc -> KindCoercion Tc -> TyReduction
mkGReflLeftRednTy ty kco
  = mkTyReduction (mkGReflLeftCo ty kco) ty
{-# INLINE mkGReflLeftRednTy #-}

mkGReflLeftMRednTy :: Type Tc -> Maybe (KindCoercion Tc) -> TyReduction
mkGReflLeftMRednTy ty mkco
  = mkTyReduction (mkGReflLeftMCo ty mkco) ty
{-# INLINE mkGReflLeftMRednTy #-}

mkGReflRightRednTy :: Type Tc -> KindCoercion Tc -> TyReduction 
mkGReflRightRednTy ty kco
  = mkTyReduction (mkGReflRightCo ty kco) (mkCastTy ty kco)
{-# INLINE mkGReflRightRednTy #-}

mkGReflRightMRednTy :: Type Tc -> Maybe (KindCoercion Tc) -> TyReduction
mkGReflRightMRednTy ty mkco
  = mkTyReduction (mkGReflRightMCo ty mkco) (mkCastTyMCo ty mkco)
{-# INLINE mkGReflRightMRednTy #-}

mkCoherenceRightRedn :: TyReduction -> KindCoercion Tc -> TyReduction
mkCoherenceRightRedn (TyReduction co1 ty2) kco
  = mkTyReduction (mkCoherenceRightCo ty2 kco co1) (mkCastTy ty2 kco)
{-# INLINE mkCoherenceRightRedn #-}

mkCoherenceRightMRedn :: TyReduction -> Maybe (KindCoercion Tc) -> TyReduction
mkCoherenceRightMRedn (TyReduction co1 ty2) kco
  = mkTyReduction (mkCoherenceRightMCo ty2 kco co1) (mkCastTyMCo ty2 kco)
{-# INLINE mkCoherenceRightMRedn #-}

mkCastRedn1 :: Type Tc -> KindCoercion Tc -> TyReduction -> TyReduction
mkCastRedn1 ty cast_kco (TyReduction co xi)
  = mkTyReduction (castCoercionKind1 co ty xi cast_kco) (mkCastTy xi cast_kco)
{-# INLINE mkCastRedn1 #-}

mkFunKiRedn :: FunKiFlag -> KiReduction -> KiReduction -> KiReduction
mkFunKiRedn af (KiReduction arg_co arg_ki) (KiReduction res_co res_ki)
  = mkKiReduction (mkFunKiCo af arg_co res_co) (mkFunKi af arg_ki res_ki)
{-# INLINE mkFunKiRedn #-}

mkAppRedn :: TyReduction -> TyReduction -> TyReduction
mkAppRedn (TyReduction co1 ty1) (TyReduction co2 ty2)
  = mkTyReduction (mkAppCo co1 co2) (mkAppTy ty1 ty2)
{-# INLINE mkAppRedn #-}

mkFunTyRedn :: KiReduction -> TyReduction -> TyReduction -> TyReduction
mkFunTyRedn (KiReduction kco ki) (TyReduction arg_co arg_ty) (TyReduction res_co res_ty)
  = mkTyReduction (mkTyFunCo kco arg_co res_co) (mkFunTy ki arg_ty res_ty)
{-# INLINE mkFunTyRedn #-}

mkHomoForAllRedn :: [ForAllBinder (TyVar Tc)] -> TyReduction -> TyReduction
mkHomoForAllRedn bndrs (TyReduction co ty) = pprPanic "mkHomoForAllRedn" (ppr bndrs $$ ppr co $$ ppr ty)
{-# INLINE mkHomoForAllRedn #-}

mkReflKiCoRedn :: KindCoercion Tc -> TyReduction
mkReflKiCoRedn kco = mkTyReduction (mkReflTyCo kco_ty) kco_ty
  where
    kco_ty = KindCoercion kco
{-# INLINE mkReflKiCoRedn #-}

data TyReductions = TyReductions [TypeCoercion Tc] [Type Tc]
data KiReductions = KiReductions [KindCoercion Tc] [MonoKind Tc]

mkTyReductions :: [TypeCoercion Tc] -> [Type Tc] -> TyReductions
mkTyReductions cos tys = TyReductions cos tys
{-# INLINE mkTyReductions #-}

mkAppRedns :: TyReduction -> TyReductions -> TyReduction
mkAppRedns (TyReduction co ty) (TyReductions cos tys)
  = mkTyReduction (mkAppCos co cos) (mkAppTys ty tys)
{-# INLINE mkAppRedns #-}

mkTyConAppRedn :: TyCon Tc -> TyReductions -> TyReduction
mkTyConAppRedn tc (TyReductions cos tys)
  = mkTyReduction (mkTyConAppCo tc cos) (mkTyConApp tc tys)
{-# INLINE mkTyConAppRedn #-}

{-# INLINE unzipRedns #-}
unzipRedns :: [TyReduction] -> TyReductions
unzipRedns = foldr accRedn (TyReductions [] [])
  where
    accRedn (TyReduction co ty) (TyReductions cos tys)
      = TyReductions (co:cos) (ty:tys)

{- *********************************************************************
*                                                                      *
     Simplifying types
*                                                                      *
********************************************************************* -}

data LiftingContext p = LC (Subst p Tc) (LiftCoEnv p)

instance Outputable (LiftingContext p) where
  ppr (LC _ env) = hang (text "LiftingContext:") 2 (ppr env)

type LiftCoEnv p = VarEnv (KiVar p) (KindCoercion Tc)

emptyLiftingContext :: KiVarSet p -> LiftingContext p
emptyLiftingContext is
  = LC (mkEmptySubst (emptyVarSet, emptyVarSet, is) (emptyVarSet, emptyVarSet, emptyVarSet))
       emptyVarEnv

liftCoSubst :: HasDebugCallStack => LiftingContext p -> MonoKind p -> KindCoercion Tc
{-# INLINE liftCoSubst #-}
liftCoSubst lc@(LC subst env) ki
  | isEmptyVarEnv env = mkReflKiCo (substMonoKi subst ki)
  | otherwise = ki_co_subst lc ki

extendLiftingContext
  :: LiftingContext p
  -> KiVar p
  -> KindCoercion Tc
  -> LiftingContext p
extendLiftingContext  (LC subst env) kv kco
  | Just ki <- isReflKiCo_maybe kco
  = LC (extendKvSubst subst kv ki) env
  | otherwise
  = LC subst (extendVarEnv env kv kco)

extendLiftingContextAndInScope
  :: LiftingContext p
  -> KiVar p
  -> KindCoercion Tc
  -> LiftingContext p
extendLiftingContextAndInScope (LC subst env) kv kco
  = extendLiftingContext
    (LC (extendSubstInScopeSetsSets subst $
          (\(kcv, kv) -> (emptyVarSet, kcv, kv)) (varsOfKindCoercion kco))
        env) kv kco

zapLiftingContext :: LiftingContext p -> LiftingContext p
zapLiftingContext (LC subst _) = LC (zapSubst subst) emptyVarEnv

ki_co_subst :: forall p. LiftingContext p -> MonoKind p -> KindCoercion Tc
ki_co_subst @p !lc ki = go ki
  where
    go :: MonoKind p -> KindCoercion Tc
    go (KiVarKi kv) = liftKiCoSubstKiVar lc kv
    go (FunKi af k1 k2) = mkFunKiCo af (go k1) (go k2)
    go (BIKi bi) = mkReflKiCo $ BIKi bi
    go other = pprPanic "ki_co_subst" (ppr other)

liftKiCoSubstKiVar :: LiftingContext p -> KiVar p -> KindCoercion Tc
liftKiCoSubstKiVar (LC subst env) kv
  | Just co_arg <- lookupVarEnv env kv
  = co_arg
  | otherwise
  = mkReflKiCo (substKiVar subst kv)

data ArgsReductions
  = ArgsReductions {-# UNPACK #-} !TyReductions !(Maybe (KindCoercion Tc))

{-
This is kind of a mess:
The list of PiKiBinders *can* be longer than the list of args.
This is ok, but when it is the case, the left over binders should
all be Anon, i.e., type args, NOT named foralled ki vars.
This should be true since the compiler elaborates the passage of all ki vars,
but I can't think of a consice way to express this in the types of things.
At some point this could take, as arguments,
  [(NamedKiBinder, TyReduction)], [AnonKiBinder], and [TyReduction]
so that the called ensures all NamedKiBinders are accounted for.
Doesn't seem worth it for now.

In the FUTURE:
'Type' will be split into several related data types,
just like 'Kind' and 'MonoKind'.
In that case, we will be able to have a data type that cannot bind foralled KiVars,
whose kind is always 'MonoKind', making all this easier.
-}
{-# INLINE simplifyArgsWorker #-}
simplifyArgsWorker
  :: forall p. HasDebugCallStack
  => [PiKiBinder p]
  -> MonoKind p
  -> KiVarSet p
  -> [TyReduction]
  -> ArgsReductions
simplifyArgsWorker @p orig_ki_binders orig_inner_ki orig_fvs orig_simplified_args
  = go orig_lc orig_ki_binders orig_inner_ki orig_simplified_args
  where
    orig_lc = emptyLiftingContext orig_fvs

    go :: LiftingContext p
       -> [PiKiBinder p]
       -> MonoKind p
       -> [TyReduction]
       -> ArgsReductions
    go !lc binders inner_ki [] = ArgsReductions (mkTyReductions [] []) kind_co
      where
        final_kind = case mkPiKis binders (Mono inner_ki) of
                       Mono ki -> ki
                       other -> pprPanic "simplifyArgsWorker final_kind not Mono"
                         $ vcat [ text "orig_ki_binders =" <+> ppr orig_ki_binders
                                , text "orig_inner_ki =" <+> ppr orig_inner_ki
                                , text "orig_simplified_args =" <+> ppr orig_simplified_args
                                , text "binders =" <+> ppr binders
                                , text "inner_ki =" <+> ppr inner_ki ]
        kind_co | noFreeVarsOfMonoKind final_kind = Nothing
                | otherwise = Just $ liftCoSubst lc final_kind

    go lc (Anon binder _ : binders) inner_ki (arg_redn:arg_redns)
      = let !kind_co = liftCoSubst lc binder
            !(TyReduction casted_co casted_xi) = mkCoherenceRightRedn arg_redn kind_co
            !new_lc = lc
            !(ArgsReductions (TyReductions cos xis) final_kind_co)
              = go new_lc binders inner_ki arg_redns
        in ArgsReductions (TyReductions (casted_co:cos) (casted_xi:xis)) final_kind_co

    go lc (Named kv : binders) inner_ki (TyReduction co xi : arg_redns)
      = let !new_lc = extendLiftingContextAndInScope lc kv (unsafeToKiCo co)
            !(ArgsReductions (TyReductions cos xis) final_kind_co)
              = go new_lc binders inner_ki arg_redns
        in ArgsReductions (TyReductions (co:cos) (xi:xis)) final_kind_co

    go lc [] inner_ki arg_redns = panic "simplifyArgsWorker last case"
      -- POTENTIAL FIX: use zapSubst :: Subst p p' -> Subst new_p p'
    
      -- = let kco1 = liftCoSubst lc inner_ki
      --       kco1_kind@(_, Pair rewritten_kind _) = kiCoercionParts kco1
      --       unrewritten_tys = map reductionOriginalType arg_redns
      --       (arg_cos, res_co) = decomposePiCos kco1 kco1_kind unrewritten_tys
      --       casted_args
      --         = assertPpr (equalLength arg_redns arg_cos) (ppr arg_redns $$ ppr arg_cos)
      --           $ zipWith mkCoherenceRightRedn arg_redns arg_cos

      --       zapped_lc = zapLiftingContext lc
      --       (bndrs, new_inner) = splitMonoPiKis rewritten_kind

      --       -- The bellow doesn't work b/c bndrs and new_inner are phase 'Tc', since they
      --       -- result from 'liftCoSubst' above.
      --       -- Calling 'simplifyArgsWorker' again is the same as calling 'go' with the
      --       -- zapped lifting context.
      --       -- May be slightly less efficient, but should be correct.
      --       -- This case should be very rare anyway.
      --       ArgsReductions redns_out res_co_out = go zapped_lc bndrs new_inner casted_args
      --       -- ArgsReductions redns_out res_co_out
      --       --   = simplifyArgsWorker bndrs new_inner orig_fvs casted_args
      --   in pprTrace "simplifyArgsWorker rare branch" (ppr inner_ki $$ ppr arg_redns $$ ppr lc) $
      --      ArgsReductions redns_out (res_co `mkTransMKiCoR` res_co_out)

    unsafeToKiCo (LiftKCo kco) = kco
    unsafeToKiCo other = pprPanic "unsageToKiCo" (ppr other)
