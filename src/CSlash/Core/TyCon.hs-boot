{-# LANGUAGE RoleAnnotations #-}

module CSlash.Core.TyCon where

import {-# SOURCE #-} CSlash.Types.Name

import qualified Data.Data as Data

type role TyCon nominal
data TyCon p

tyConName :: TyCon p -> Name

instance (Data.Typeable p) => Data.Data (TyCon p) 