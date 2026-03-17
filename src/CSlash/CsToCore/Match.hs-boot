module CSlash.CsToCore.Match where

import CSlash.Cs
import CSlash.Types.Var.Id 
import CSlash.Core.Type
import CSlash.CsToCore.Monad
import CSlash.Core
import CSlash.Cs.Expr 

matchSinglePatVar
  :: Id Zk
  -> Maybe CoreExpr
  -> CsMatchContextRn
  -> LPat Zk
  -> Type Zk
  -> MatchResult CoreExpr
  -> DsM (MatchResult CoreExpr)
