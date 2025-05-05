module CSlash.Core.Type.FVs where

import CSlash.Core.Type.Rep (Type)
import CSlash.Types.Var.Set (TyVarSet)
import Data.Monoid (Endo)

deep_ty :: Type -> Endo TyVarSet
