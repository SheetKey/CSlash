module CSlash.Core.Predicate where

import CSlash.Core.Rep (Type)
import CSlash.Cs.Pass (HasPass)

isTyCoVarType :: HasPass p pass => Type p -> Bool
