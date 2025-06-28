module CSlash.Core.Reduction where

-- import GHC.Core.Class      ( Class(classTyCon) )
-- import GHC.Core.Coercion
-- import GHC.Core.Predicate  ( mkClassPred )
import CSlash.Core.TyCon ( TyCon )
import CSlash.Core.Type
import CSlash.Core.Kind

import CSlash.Data.Pair ( Pair(Pair) )
import CSlash.Data.List.Infinite ( Infinite (..) )
import qualified CSlash.Data.List.Infinite as Inf

import CSlash.Types.Var ( VarBndr(..), setVarKind )
import CSlash.Types.Var.Env ( mkInScopeSet )
import CSlash.Types.Var.Set ( TyVarSet )
import CSlash.Tc.Utils.TcType (AnyMonoKind, AnyKindCoercion)

import CSlash.Utils.Misc ( HasDebugCallStack, equalLength )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

{- *********************************************************************
*                                                                      *
     Reductions
*                                                                      *
********************************************************************* -}

data Reduction = ReductionKi
  { reductionKindCoercion :: AnyKindCoercion 
  , reductionReducedKind :: !AnyMonoKind }

mkReductionKi :: AnyKindCoercion -> AnyMonoKind -> Reduction
mkReductionKi co ki = ReductionKi co ki
{-# INLINE mkReductionKi #-}

instance Outputable Reduction where
  ppr redn@(ReductionKi {}) = braces $ vcat
    [ text "reductionOriginalKind:" <+> ppr (reductionOriginalKind redn)
    , text "reductionReducedKind:" <+> ppr (reductionReducedKind redn)
    , text "reductionKindCoercion:" <+> ppr (reductionKindCoercion redn) ]

reductionOriginalKind :: Reduction -> AnyMonoKind
reductionOriginalKind = kicoercionLKind . reductionKindCoercion
{-# INLINE reductionOriginalKind #-}

mkTransRedn :: AnyKindCoercion -> Reduction -> Reduction
mkTransRedn co1 redn@(ReductionKi co2 _) = redn { reductionKindCoercion = co1 `mkTransKiCo` co2 }
{-# INLINE mkTransRedn #-}

mkReflRednKi :: AnyMonoKind -> Reduction
mkReflRednKi ki = mkReductionKi (mkReflKiCo ki) ki

mkFunKiRedn :: FunKiFlag -> Reduction -> Reduction -> Reduction
mkFunKiRedn af (ReductionKi arg_co arg_ki) (ReductionKi res_co res_ki)
  = mkReductionKi (mkFunKiCo af arg_co res_co) (mkFunKi af arg_ki res_ki)
{-# INLINE mkFunKiRedn #-}

data Reductions = Reductions [AnyKindCoercion] [AnyMonoKind]

mkKiConAppRedn :: KiCon -> Reductions -> Reduction
mkKiConAppRedn kc (Reductions cos kis) = mkReductionKi (mkKiConAppCo kc cos) (mkKiConApp kc kis)
{-# INLINE mkKiConAppRedn #-}

{-# INLINE unzipRedns #-}
unzipRedns :: [Reduction] -> Reductions
unzipRedns = foldr accRedn (Reductions [] [])
  where
    accRedn (ReductionKi co ki) (Reductions cos kis)
      = Reductions (co:cos) (ki:kis)
