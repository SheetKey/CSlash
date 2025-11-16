{-# LANGUAGE BangPatterns #-}

module CSlash.Core.Reduction where

-- import GHC.Core.Class      ( Class(classTyCon) )
-- import GHC.Core.Coercion
-- import GHC.Core.Predicate  ( mkClassPred )
import CSlash.Core.TyCon ( TyCon, AnyTyCon )
import CSlash.Core.Type
import CSlash.Core.Type.Rep
import CSlash.Core.Kind
import CSlash.Core.Kind.Subst
import CSlash.Core.Kind.FVs

import CSlash.Data.Pair ( Pair(Pair) )
import CSlash.Data.List.Infinite ( Infinite (..) )
import qualified CSlash.Data.List.Infinite as Inf

import CSlash.Types.Var ( VarBndr(..), PiKiBinder(..), setVarKind )
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set ( TyVarSet, AnyKiVarSet )
import CSlash.Tc.Utils.TcType (AnyMonoKind, AnyKindCoercion, AnyType, AnyKvSubst)

import CSlash.Utils.Misc ( HasDebugCallStack, equalLength )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

{- *********************************************************************
*                                                                      *
     Reductions
*                                                                      *
********************************************************************* -}

data KiReduction = KiReduction
  { reductionKindCoercion :: AnyKindCoercion 
  , reductionReducedKind :: !AnyMonoKind }

data TyReduction = TyReduction
  { reductionTypeCoercion :: AnyTypeCoercion
  , reductionReducedType :: !AnyType }

mkTyReduction :: AnyTypeCoercion -> AnyType -> TyReduction
mkTyReduction co ty = TyReduction co ty
{-# INLINE mkTyReduction #-}

mkKiReduction :: AnyKindCoercion -> AnyMonoKind -> KiReduction
mkKiReduction co ki = KiReduction co ki
{-# INLINE mkKiReduction #-}

data HetTyReduction = HetTyReduction TyReduction (Maybe AnyKindCoercion)

mkHetTyReduction :: TyReduction -> Maybe AnyKindCoercion -> HetTyReduction
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

reductionOriginalKind :: KiReduction -> AnyMonoKind
reductionOriginalKind = kicoercionLKind . reductionKindCoercion
{-# INLINE reductionOriginalKind #-}

reductionOriginalType :: TyReduction -> AnyType
reductionOriginalType = tycoercionLType . reductionTypeCoercion
{-# INLINE reductionOriginalType #-}

mkTransRedn :: AnyKindCoercion -> KiReduction -> KiReduction
mkTransRedn co1 redn@(KiReduction co2 _) = redn { reductionKindCoercion = co1 `mkTransKiCo` co2 }
{-# INLINE mkTransRedn #-}

mkTransTyRedn :: AnyTypeCoercion -> TyReduction -> TyReduction
mkTransTyRedn co1 redn@(TyReduction co2 _)
  = redn { reductionTypeCoercion = co1 `mkTyTransCo` co2 }
{-# INLINE mkTransTyRedn #-}

mkReflRednKi :: AnyMonoKind -> KiReduction
mkReflRednKi ki = mkKiReduction (mkReflKiCo ki) ki

mkReflRednTy :: AnyType -> TyReduction
mkReflRednTy ty = mkTyReduction (mkReflTyCo ty) ty

mkGReflLeftRednTy :: AnyType -> AnyKindCoercion -> TyReduction
mkGReflLeftRednTy ty kco
  = mkTyReduction (mkGReflLeftCo ty kco) ty
{-# INLINE mkGReflLeftRednTy #-}

mkGReflLeftMRednTy :: AnyType -> Maybe AnyKindCoercion -> TyReduction
mkGReflLeftMRednTy ty mkco
  = mkTyReduction (mkGReflLeftMCo ty mkco) ty
{-# INLINE mkGReflLeftMRednTy #-}

mkGReflRightRednTy :: AnyType -> AnyKindCoercion -> TyReduction 
mkGReflRightRednTy ty kco
  = mkTyReduction (mkGReflRightCo ty kco) (mkCastTy ty kco)
{-# INLINE mkGReflRightRednTy #-}

mkGReflRightMRednTy :: AnyType -> Maybe AnyKindCoercion -> TyReduction
mkGReflRightMRednTy ty mkco
  = mkTyReduction (mkGReflRightMCo ty mkco) (mkCastTyMCo ty mkco)
{-# INLINE mkGReflRightMRednTy #-}

mkCoherenceRightRedn :: TyReduction -> AnyKindCoercion -> TyReduction
mkCoherenceRightRedn (TyReduction co1 ty2) kco
  = mkTyReduction (mkCoherenceRightCo ty2 kco co1) (mkCastTy ty2 kco)
{-# INLINE mkCoherenceRightRedn #-}

mkCoherenceRightMRedn :: TyReduction -> Maybe AnyKindCoercion -> TyReduction
mkCoherenceRightMRedn (TyReduction co1 ty2) kco
  = mkTyReduction (mkCoherenceRightMCo ty2 kco co1) (mkCastTyMCo ty2 kco)
{-# INLINE mkCoherenceRightMRedn #-}

mkCastRedn1 :: AnyType -> AnyKindCoercion -> TyReduction -> TyReduction
mkCastRedn1 ty kco (TyReduction co xi)
  = panic "mkCastRedn1"
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

mkHomoForAllRedn :: [ForAllBinder (AnyTyVar AnyKiVar)] -> TyReduction -> TyReduction
mkHomoForAllRedn bndrs (TyReduction co ty) = pprPanic "mkHomoForAllRedn" (ppr bndrs $$ ppr co $$ ppr ty)
{-# INLINE mkHomoForAllRedn #-}

mkReflKiCoRedn :: AnyKindCoercion -> TyReduction
mkReflKiCoRedn kco = mkTyReduction (mkReflTyCo kco_ty) kco_ty
  where
    kco_ty = KindCoercion kco
{-# INLINE mkReflKiCoRedn #-}

data TyReductions = TyReductions [AnyTypeCoercion] [AnyType]
data KiReductions = KiReductions [AnyKindCoercion] [AnyMonoKind]

mkTyReductions :: [AnyTypeCoercion] -> [AnyType] -> TyReductions
mkTyReductions cos tys = TyReductions cos tys
{-# INLINE mkTyReductions #-}

mkAppRedns :: TyReduction -> TyReductions -> TyReduction
mkAppRedns (TyReduction co ty) (TyReductions cos tys)
  = mkTyReduction (mkAppCos co cos) (mkAppTys ty tys)
{-# INLINE mkAppRedns #-}

mkTyConAppRedn :: AnyTyCon -> TyReductions -> TyReduction
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

data LiftingContext = LC AnyKvSubst LiftCoEnv

instance Outputable LiftingContext where
  ppr (LC _ env) = hang (text "LiftingContext:") 2 (ppr env)

type LiftCoEnv = MkVarEnv AnyKiVar AnyKindCoercion

emptyLiftingContext :: InScopeSet AnyKiVar -> LiftingContext
emptyLiftingContext is = LC (mkEmptyKvSubst is) emptyVarEnv

liftCoSubst :: HasDebugCallStack => LiftingContext -> AnyMonoKind -> AnyKindCoercion
{-# INLINE liftCoSubst #-}
liftCoSubst lc@(LC subst env) ki
  | isEmptyVarEnv env = mkReflKiCo (substMonoKi subst ki)
  | otherwise = ki_co_subst lc ki

extendLiftingContext
  :: LiftingContext
  -> AnyKiVar
  -> AnyKindCoercion
  -> LiftingContext
extendLiftingContext  (LC subst env) kv kco
  | Just ki <- isReflKiCo_maybe kco
  = LC (extendKvSubst subst kv ki) env
  | otherwise
  = LC subst (extendVarEnv env kv kco)

extendLiftingContextAndInScope
  :: LiftingContext
  -> AnyKiVar
  -> AnyKindCoercion
  -> LiftingContext
extendLiftingContextAndInScope (LC subst env) kv kco
  = extendLiftingContext
    (LC (extendKvSubstInScopeSet subst (snd $ varsOfKindCoercion kco)) env) kv kco

zapLiftingContext :: LiftingContext -> LiftingContext
zapLiftingContext (LC subst _) = LC (zapKvSubst subst) emptyVarEnv

ki_co_subst :: LiftingContext -> AnyMonoKind -> AnyKindCoercion
ki_co_subst !lc ki = go ki
  where
    go :: AnyMonoKind -> AnyKindCoercion
    go (KiVarKi kv) = liftKiCoSubstKiVar lc kv
    go (FunKi af k1 k2) = mkFunKiCo af (go k1) (go k2)
    go (BIKi bi) = mkReflKiCo $ BIKi bi
    go other = pprPanic "ki_co_subst" (ppr other)

liftKiCoSubstKiVar :: LiftingContext -> AnyKiVar -> AnyKindCoercion
liftKiCoSubstKiVar (LC subst env) kv
  | Just co_arg <- lookupVarEnv env kv
  = co_arg
  | otherwise
  = mkReflKiCo (substKiVar subst kv)

data ArgsReductions
  = ArgsReductions {-# UNPACK #-} !TyReductions !(Maybe AnyKindCoercion)

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
  :: HasDebugCallStack
  => [PiKiBinder AnyKiVar]
  -> AnyMonoKind
  -> AnyKiVarSet
  -> [TyReduction]
  -> ArgsReductions
simplifyArgsWorker orig_ki_binders orig_inner_ki orig_fvs orig_simplified_args
  = go orig_lc orig_ki_binders orig_inner_ki orig_simplified_args
  where
    orig_lc = emptyLiftingContext $ mkInScopeSet orig_fvs

    go :: LiftingContext
       -> [PiKiBinder AnyKiVar]
       -> AnyMonoKind
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

    go lc [] inner_ki arg_redns
      = let kco1 = liftCoSubst lc inner_ki
            kco1_kind = kiCoercionParts kco1
            unrewritten_tys = map reductionOriginalType arg_redns
            (arg_cos, res_co) = decomposePiCos kco1 kco1_kind unrewritten_tys
            casted_args
              = assertPpr (equalLength arg_redns arg_cos) (ppr arg_redns $$ ppr arg_cos)
                $ zipWith mkCoherenceRightRedn arg_redns arg_cos

            zapped_lc = zapLiftingContext lc
            (_, Pair rewritten_kind _) = kco1_kind
            (bndrs, new_inner) = splitMonoPiKis rewritten_kind

            ArgsReductions redns_out res_co_out = go zapped_lc bndrs new_inner casted_args
        in ArgsReductions redns_out (res_co `mkTransMKiCoR` res_co_out)

    unsafeToKiCo (LiftKCo kco) = kco
    unsafeToKiCo other = pprPanic "unsageToKiCo" (ppr other)
