module CSlash.Tc.Gen.Expr where

import CSlash.Cs
-- import CSlash.Cs.Syn.Type
import CSlash.Rename.Utils
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.Unify
import CSlash.Types.Basic
import CSlash.Types.Error
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.Map
import CSlash.Types.Unique.Set
import CSlash.Core.Kind
import CSlash.Core.UsageEnv
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Instantiate
-- import CSlash.Tc.Gen.App
-- import CSlash.Tc.Gen.Head
-- import CSlash.Tc.Gen.Bind        ( tcLocalBinds )
import CSlash.Rename.Env         ( addUsedGRE )
import CSlash.Tc.Utils.Env
-- import CSlash.Tc.Gen.Arrow
-- import CSlash.Tc.Gen.Match( tcBody, tcLambdaMatches, tcCaseMatches
--                           , tcGRHSList, tcDoStmts )
import CSlash.Tc.Gen.CsType
import CSlash.Tc.Utils.TcMType
import CSlash.Tc.Zonk.TcType
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.TcType as TcType
import CSlash.Types.Id
import CSlash.Types.Id.Info
import CSlash.Core.ConLike
import CSlash.Core.DataCon
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Types.Name.Reader
import CSlash.Core.TyCon
import CSlash.Core.Type
import CSlash.Tc.Types.Evidence
import CSlash.Builtin.Types
import CSlash.Builtin.Names
-- import CSlash.Builtin.Uniques ( mkBuiltinUnique )
import CSlash.Driver.DynFlags
import CSlash.Types.SrcLoc
import CSlash.Utils.Misc
import CSlash.Data.List.SetOps
import CSlash.Data.Maybe
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic

import Control.Monad
import qualified Data.List.NonEmpty as NE


{- *********************************************************************
*                                                                      *
            Main wrappers
*                                                                      *
********************************************************************* -}

tcPolyLExpr :: LCsExpr Rn -> ExpSigmaType -> TcM (LCsExpr Tc)
tcPolyLExpr = panic "tcPolyLExpr"

{- *********************************************************************
*                                                                      *
        tcExpr: the main expression typechecker
*                                                                      *
********************************************************************* -}

tcInferRhoNC :: LCsExpr Rn -> TcM (LCsExpr Tc, AnyRhoType)
tcInferRhoNC = panic "tcInferRhoNC"

tcCheckMonoExpr :: LCsExpr Rn -> AnyRhoType -> TcM (LCsExpr Tc)
tcCheckMonoExpr = panic "tcCheckMonoExpr"

tcExpr :: CsExpr Rn -> ExpRhoType -> TcM (CsExpr Tc)
tcExpr = panic "tcExpr"
