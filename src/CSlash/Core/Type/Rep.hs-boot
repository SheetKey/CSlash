module CSlash.Core.Type.Rep where

import {-# SOURCE #-} CSlash.Core.TyCon (TyCon)
import {-# SOURCE #-} CSlash.Types.Var (AsAnyTy, AsGenericTy)

data Type tv kv

instance AsGenericTy Type

type PredType = Type

mkNakedTyConTy :: TyCon tv kv -> Type tv kv

instance AsAnyTy Type