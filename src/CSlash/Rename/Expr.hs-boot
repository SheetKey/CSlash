{-# LANGUAGE ConstraintKinds #-}

module CSlash.Rename.Expr where

import CSlash.Types.Name
import CSlash.Cs
import CSlash.Types.Name.Set ( FreeVars )
import CSlash.Tc.Types
import CSlash.Utils.Outputable  ( Outputable )

rnExpr :: CsExpr Ps -> RnM (CsExpr Rn, FreeVars)

rnLExpr :: LCsExpr Ps -> RnM (LCsExpr Rn, FreeVars)

type RnStmtsAnnoBody body
  = ( Outputable (body Ps) )

rnStmts :: RnStmtsAnnoBody body => CsStmtContextRn
        -> (body Ps -> RnM (body Rn, FreeVars))
        -> [LStmt Ps (LocatedA (body Ps))]
        -> ([Name] -> RnM (thing, FreeVars))
        -> RnM (([LStmt Rn (LocatedA (body Rn))], thing), FreeVars)
