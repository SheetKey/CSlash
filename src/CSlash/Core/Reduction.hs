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

import CSlash.Types.Var ( VarBndr(..), setTyVarKind )
import CSlash.Types.Var.Env ( mkInScopeSet )
import CSlash.Types.Var.Set ( TyVarSet )

import CSlash.Utils.Misc ( HasDebugCallStack, equalLength )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic ( assertPpr )

{- *********************************************************************
*                                                                      *
     Reductions
*                                                                      *
********************************************************************* -}

data Reduction
  = ReductionKi
    { reductionKind :: Kind
    , reductionReducedKind :: !Kind }
  | ReflRednKi !Kind

mkReductionKi :: Kind -> Kind -> Reduction
mkReductionKi = ReductionKi
{-# INLINE mkReductionKi #-}

instance Outputable Reduction where
  ppr (ReductionKi og new) = braces $ vcat [ text "reductionOriginalKind:" <+> ppr og
                                           , text "reductionReducedKind:" <+> ppr new ]
  ppr (ReflRednKi new) = braces $ vcat [ text "reductionReducedKind:" <+> ppr new ]

mkTransRedn :: Kind -> Reduction -> Reduction
mkTransRedn og_kind (ReductionKi _ newest_kind) = ReductionKi og_kind newest_kind
mkTransRedn og_kind (ReflRednKi newest_kind) = ReductionKi og_kind newest_kind

mkReflRednKi :: Kind -> Reduction
mkReflRednKi = ReflRednKi

mkFunKiRedn :: FunKdFlag -> Reduction -> Reduction -> Reduction
mkFunKiRedn f (ReductionKi arg_og arg_new) (ReductionKi res_og res_new)
  = mkReductionKi (FunKd f arg_og res_og) (FunKd f arg_new res_new)
mkFunKiRedn f (ReflRednKi arg_new) (ReductionKi res_og res_new)
  = mkReductionKi (FunKd f arg_new res_og) (FunKd f arg_new res_new)
mkFunKiRedn f (ReductionKi arg_og arg_new) (ReflRednKi res_new)
  = mkReductionKi (FunKd f arg_og res_new) (FunKd f arg_new res_new)
mkFunKiRedn f (ReflRednKi arg_new) (ReflRednKi res_new)
  = mkReflRednKi (FunKd f arg_new res_new)
{-# INLINE mkFunKiRedn #-}
