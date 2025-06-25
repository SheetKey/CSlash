module CSlash.Core.Type.Rep where

import {-# SOURCE #-} CSlash.Core.TyCon (TyCon)
import {-# SOURCE #-} CSlash.Types.Var (AsAnyTy)

data Type tv kv

mkNakedTyConTy :: TyCon tv kv -> Type tv kv

instance AsAnyTy Type