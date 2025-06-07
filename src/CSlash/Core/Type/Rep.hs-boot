module CSlash.Core.Type.Rep where

import {-# SOURCE #-} CSlash.Core.TyCon (TyCon)

data Type tv kv

mkNakedTyConTy :: TyCon tv kv -> Type tv kv
