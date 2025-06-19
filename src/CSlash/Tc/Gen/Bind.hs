module CSlash.Tc.Gen.Bind where

-- import {-# SOURCE #-} GHC.Tc.Gen.Match ( tcGRHSsPat, tcFunBindMatches )
-- import {-# SOURCE #-} GHC.Tc.Gen.Expr  ( tcCheckMonoExpr )
-- import {-# SOURCE #-} GHC.Tc.TyCl.PatSyn ( tcPatSynDecl, tcPatSynBuilderBind )

import CSlash.Types.Tickish ({-CoreTickish,-} GenTickish (..))
-- import GHC.Types.CostCentre (mkUserCC, mkDeclCCFlavour)
import CSlash.Driver.DynFlags
import CSlash.Data.FastString
import CSlash.Cs

-- import GHC.Rename.Bind ( rejectBootDecls )

import CSlash.Tc.Errors.Types
-- import GHC.Tc.Gen.Sig
-- import GHC.Tc.Utils.Concrete ( hasFixedRuntimeRep_syntactic )
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.Env
-- import GHC.Tc.Utils.Unify
import CSlash.Tc.Solver
-- import GHC.Tc.Types.Evidence
-- import GHC.Tc.Types.Constraint
-- import GHC.Core.Predicate
-- import GHC.Core.UsageEnv ( bottomUE )
-- import GHC.Tc.Gen.HsType
-- import GHC.Tc.Gen.Pat
import CSlash.Tc.Utils.TcMType
-- import GHC.Tc.Instance.Family( tcGetFamInstEnvs )
import CSlash.Tc.Utils.TcType
-- import GHC.Tc.Validity (checkValidType, checkEscapingKind)
import CSlash.Tc.Zonk.TcType
-- import GHC.Core.Reduction ( Reduction(..) )
-- import GHC.Core.Multiplicity
-- import GHC.Core.FamInstEnv( normaliseType )
-- import GHC.Core.Class   ( Class )
-- import GHC.Core.Coercion( mkSymCo )
-- import CSlash.Core.Type (mkStrLitTy, tidyOpenType, mkCastTy)
-- import CSlash.Core.Type.Ppr( pprTyVars )

-- import CSlash.Builtin.Types ( mkConstraintTupleTy, multiplicityTy, oneDataConTy  )
import CSlash.Builtin.Types.Prim
import CSlash.Unit.Module

import CSlash.Types.SourceText
import CSlash.Types.Id
import CSlash.Types.Var as Var
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env( MkTidyEnv, TyVarEnv, {-mkVarEnv,-} lookupVarEnv )
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Name.Env
import CSlash.Types.SourceFile
import CSlash.Types.SrcLoc

import CSlash.Utils.Error
import CSlash.Utils.Misc
import CSlash.Types.Basic
import CSlash.Types.CompleteMatch
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic
-- import CSlash.Builtin.Names( ipClassName )
import CSlash.Types.Unique.FM
import CSlash.Types.Unique.DSet
import CSlash.Types.Unique.Set

import CSlash.Data.Bag
import CSlash.Data.Graph.Directed
import CSlash.Data.Maybe

import Control.Monad
import Data.Foldable (find)

tcTopBinds :: [(RecFlag, LCsBinds Rn)] -> [LSig Rn] -> TcM (TcGblEnv, TcLclEnv)
tcTopBinds binds sigs = assertPpr (null binds && null sigs) (ppr (snd <$> binds) $$ ppr sigs)
                        $ getEnvs
