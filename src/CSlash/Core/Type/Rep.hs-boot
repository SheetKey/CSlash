module CSlash.Core.Type.Rep where

import {-# SOURCE #-} CSlash.Core.TyCon (TyCon)

data Type

mkNakedTyConTy :: TyCon -> Type
