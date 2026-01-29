module CSlash.CsToCore.Expr where

-- import GHC.HsToCore.Match
-- import GHC.HsToCore.Match.Literal
import CSlash.CsToCore.Binds
-- import GHC.HsToCore.GuardedRHSs
-- import GHC.HsToCore.ListComp
-- import GHC.HsToCore.Utils
-- import GHC.HsToCore.Arrows
import CSlash.CsToCore.Monad
-- import GHC.HsToCore.Pmc
-- import GHC.HsToCore.Errors.Types
import CSlash.Types.SourceText
import CSlash.Types.Name hiding (varName)
-- import GHC.HsToCore.Quote
-- import GHC.HsToCore.Ticks (stripTicksTopHsExpr)
import CSlash.Cs

import CSlash.Tc.Utils.TcType
import CSlash.Tc.Types.Evidence
import CSlash.Tc.Utils.Monad
import CSlash.Core.Type
import CSlash.Core.Kind
import CSlash.Core.Type.Rep
import CSlash.Core
-- import CSlash.Core.Utils
-- import CSlash.Core.Make

import CSlash.Driver.Session
-- import GHC.Types.CostCentre
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.Var.Id.Make
import CSlash.Unit.Module
import CSlash.Core.ConLike
import CSlash.Core.DataCon
import CSlash.Builtin.Types
import CSlash.Builtin.Names
import CSlash.Types.Basic
import CSlash.Types.SrcLoc
import CSlash.Types.Tickish
import CSlash.Utils.Misc
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic
-- import GHC.Core.PatSyn
import Control.Monad
import CSlash.Types.Error

{- *********************************************************************
*                                                                      *
                dsLocalBinds, dsValBinds
*                                                                      *
********************************************************************* -}

{- *********************************************************************
*                                                                      *
*              Variables, constructors, literals                       *
*                                                                      *
********************************************************************* -}


dsLExpr :: LCsExpr Zk -> DsM CoreExpr
dsLExpr (L loc e) = panic "putSrcSpanDsA loc $ dsExpr e"

dsExpr :: CsExpr Zk -> DsM CoreExpr

dsExpr (CsVar _ (L _ id)) = dsCsVar id

dsExpr other = pprPanic "dsExpr" (ppr other)


{- *********************************************************************
*                                                                      *
   Desugaring Variables
*                                                                      *
********************************************************************* -}

dsCsVar :: Id Zk -> DsM CoreExpr
dsCsVar var = return (varToCoreExpr var)
