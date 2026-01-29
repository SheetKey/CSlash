{-# LANGUAGE RoleAnnotations #-}

module CSlash.Core.TyCon where

import {-# SOURCE #-} CSlash.Types.Name

type role TyCon nominal
data TyCon p

tyConName :: TyCon p -> Name