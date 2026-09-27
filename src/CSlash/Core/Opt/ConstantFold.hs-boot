module CSlash.Core.Opt.ConstantFold where

import CSlash.Types.Name ( Name )
import {-# SOURCE #-} CSlash.Builtin.PrimOps ( PrimOp(..){-, tagToEnumKey-} )
import {-# SOURCE #-} CSlash.Core (CoreRule)


primOpRules :: Name -> PrimOp -> Maybe CoreRule
