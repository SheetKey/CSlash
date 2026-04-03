{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RoleAnnotations #-}

module CSlash.Types.Var.Id where

import {-# SOURCE #-} CSlash.Types.Var.Class
import CSlash.Cs.Pass
import CSlash.Utils.Outputable
import CSlash.Types.Unique

import Data.Data

type role Id nominal 
data Id p

instance (Typeable p) => Data (Id p)
instance Eq (Id p)
instance IsVar (Id p) 
instance IsPass p => Outputable (Id (CsPass p)) 
instance Uniquable (Id p) 

isLocalId :: Id p -> Bool
isJoinId :: Id p -> Bool
