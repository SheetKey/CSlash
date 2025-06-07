module CSlash.Core.TyCon where

import {-# SOURCE #-} CSlash.Types.Name

data TyCon tv kv

tyConName :: TyCon tv kv -> Name