module CSlash.Core.Type.FVs where

import {-# SOURCE #-} CSlash.Core.Type.Rep (Type)
import CSlash.Utils.FV

type TyFV p = FV (Type p)

fvsOfType :: Type p -> TyFV p

-- deep_ty
--   :: (Outputable tv, Outputable kv, Uniquable tv, Uniquable kv, VarHasKind tv kv)
--   => Type tv kv -> Endo (MkVarSet tv, MkVarSet kv)

