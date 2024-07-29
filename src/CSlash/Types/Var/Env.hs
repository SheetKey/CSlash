module CSlash.Types.Var.Env where

import CSlash.Types.Name.Occurrence
import CSlash.Types.Name
import CSlash.Types.Var as Var
import CSlash.Types.Var.Set
import CSlash.Types.Unique.Set
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.DFM
import CSlash.Types.Unique
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Data.Maybe
import CSlash.Utils.Outputable

{- *********************************************************************
*                                                                      *
                In-scope sets
*                                                                      *
********************************************************************* -}

newtype InScopeSet = InScope VarSet

instance Outputable InScopeSet where
  ppr (InScope s) = text "InScope" <+>
                    braces (fsep (map (ppr . Var.varName) (nonDetEltsUniqSet s)))

emptyInScopeSet :: InScopeSet
emptyInScopeSet = InScope emptyVarSet
