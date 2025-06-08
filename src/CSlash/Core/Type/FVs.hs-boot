module CSlash.Core.Type.FVs where

import CSlash.Core.Type.Rep (Type)
import CSlash.Types.Var.Set (TyVarSet)
import Data.Monoid (Endo)

-- deep_ty
--   :: (Outputable tv, Outputable kv, Uniquable tv, Uniquable kv, VarHasKind tv kv)
--   => Type tv kv -> Endo (MkVarSet tv, MkVarSet kv)

