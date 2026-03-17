module CSlash.CsToCore.Expr where

import CSlash.Cs
import CSlash.Core
import CSlash.CsToCore.Types

dsExpr :: CsExpr Zk -> DsM CoreExpr
dsLExpr :: LCsExpr Zk -> DsM CoreExpr

dsLocalBinds :: CsLocalBinds Zk -> CoreExpr -> DsM CoreExpr
