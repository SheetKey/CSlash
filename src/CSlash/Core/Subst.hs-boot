module CSlash.Core.Subst where

import CSlash.Cs.Pass
import {-# SOURCE #-} CSlash.Core.Type.Rep

fromZkType :: HasPass p pass => Type Zk -> Type p