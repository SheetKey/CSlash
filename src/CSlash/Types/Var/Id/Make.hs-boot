{-# LANGUAGE RankNTypes #-}

module CSlash.Types.Var.Id.Make where

import CSlash.Cs.Pass

import CSlash.Types.Name (Name)
import {-# SOURCE #-} CSlash.Types.Var.Id (Id)
import {-# SOURCE #-} CSlash.Core.DataCon (DataCon)

mkDataConId :: Name -> DataCon Zk -> Id Zk
