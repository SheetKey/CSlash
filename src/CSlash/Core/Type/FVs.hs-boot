module CSlash.Core.Type.FVs where

import CSlash.Cs.Pass
import {-# SOURCE #-} CSlash.Core.Rep (Type)
import CSlash.Utils.FV
import CSlash.Types.Var.Set

type TyFV p = FV (Type p)

fvsOfType :: Type p -> TyFV p

varsOfType :: HasPass p p' => Type p -> (TyVarSet p, KiCoVarSet p, KiVarSet p)
varsOfTypes :: HasPass p p' => [Type p] -> (TyVarSet p, KiCoVarSet p, KiVarSet p)

-- deep_ty
--   :: (Outputable tv, Outputable kv, Uniquable tv, Uniquable kv, VarHasKind tv kv)
--   => Type tv kv -> Endo (MkVarSet tv, MkVarSet kv)

