module CSlash.Types.RepType where

import CSlash.Types.Basic (Arity, RepArity)
import CSlash.Core.DataCon
import CSlash.Core.TyCon
import CSlash.Core.Type.Rep
import CSlash.Core.Type

import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Data.List.NonEmpty (NonEmpty (..))
import Data.List (sort)

unwrapType :: Type -> Type
unwrapType ty = inner_ty
  where
    inner_ty = go ty

    go t | Just t' <- coreView t = go t'
    go (ForAllTy _ t) = go t
    go t = t

countFunRepArgs :: Arity -> Type -> RepArity
countFunRepArgs 0 _ = 0
countFunRepArgs n ty
  | FunTy _ _arg res <- unwrapType ty
  = 1                                 -- (length (typePrimRep arg) `max` 1)
    + countFunRepArgs (n - 1) res
  | otherwise
  = pprPanic "countFunRepArgs arity greater than type can handle" (ppr (n, ty))
