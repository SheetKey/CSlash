module CSlash.Tc.Module where

import CSlash.Driver.Env
-- import GHC.Driver.Plugins
import CSlash.Driver.DynFlags
import CSlash.Driver.Config.Diagnostic

-- import GHC.Tc.Errors.Hole.Plugin ( HoleFitPluginR (..) )
-- import GHC.Tc.Errors.Types
-- import {-# SOURCE #-} GHC.Tc.Gen.Splice ( finishTH, runRemoteModFinalizers )
-- import GHC.Tc.Gen.HsType
-- import GHC.Tc.Validity( checkValidType )
-- import GHC.Tc.Gen.Match
-- import GHC.Tc.Utils.Unify( checkConstraints, tcSubTypeSigma )
-- import GHC.Tc.Zonk.Type
-- import GHC.Tc.Gen.Expr
-- import GHC.Tc.Gen.App( tcInferSigma )
import CSlash.Tc.Utils.Monad
-- import GHC.Tc.Gen.Export
-- import GHC.Tc.Types.Evidence
-- import GHC.Tc.Types.Constraint
-- import GHC.Tc.Types.Origin
-- import GHC.Tc.Instance.Family
-- import GHC.Tc.Gen.Annotation
-- import GHC.Tc.Gen.Bind
-- import GHC.Tc.Gen.Default
-- import GHC.Tc.Utils.Env
-- import GHC.Tc.Gen.Rule
-- import GHC.Tc.Gen.Foreign
-- import GHC.Tc.TyCl.Instance
-- import GHC.Tc.Utils.TcMType
import CSlash.Tc.Utils.TcType
-- import GHC.Tc.Solver
-- import GHC.Tc.TyCl
-- import GHC.Tc.Instance.Typeable ( mkTypeableBinds )
-- import GHC.Tc.Utils.Backpack
-- import GHC.Tc.Zonk.TcType

-- import GHC.Rename.Bind ( rejectBootDecls )
-- import GHC.Rename.Splice ( rnTopSpliceDecls, traceSplice, SpliceInfo(..) )
-- import GHC.Rename.HsType
-- import GHC.Rename.Expr
-- import GHC.Rename.Fixity ( lookupFixityRn )
import CSlash.Rename.Names
-- import GHC.Rename.Env
-- import GHC.Rename.Module
-- import GHC.Rename.Doc
-- import GHC.Rename.Utils ( mkNameClashErr )

-- import GHC.Iface.Decl    ( coAxiomToIfaceDecl )
-- import CSlash.Iface.Env     ( externaliseName )
import CSlash.Iface.Load

-- import CSlash.Builtin.Types ( mkListTy, anyTypeOfKind )
import CSlash.Builtin.Names
import CSlash.Builtin.Utils

import CSlash.Cs --hiding ( FunDep(..) )
import CSlash.Cs.Dump

-- import GHC.Core.PatSyn
-- import GHC.Core.Predicate ( classMethodTy )
-- import GHC.Core.InstEnv
import CSlash.Core.TyCon
import CSlash.Core.DataCon
import CSlash.Core.Type.Rep
import CSlash.Core.Type
-- import GHC.Core.Class
-- import GHC.Core.Coercion.Axiom
-- import GHC.Core.Reduction ( Reduction(..) )
-- import CSlash.Core.Type.Ppr( debugPprType )
-- import GHC.Core.FamInstEnv
--    ( FamInst, pprFamInst, famInstsRepTyCons, orphNamesOfFamInst
--    , famInstEnvElts, extendFamInstEnvList, normaliseType )

import CSlash.Parser.Header       ( mkPrelImports )

-- import GHC.IfaceToCore

-- import GHC.Runtime.Context

import CSlash.Utils.Error
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc
import CSlash.Utils.Logger

import CSlash.Types.Error
import CSlash.Types.Name.Reader
import CSlash.Types.Fixity.Env
import CSlash.Types.Id as Id
import CSlash.Types.Id.Info( IdDetails(..) )
import CSlash.Types.Var.Env
import CSlash.Types.TypeEnv
import CSlash.Types.Unique.FM
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Types.Avail
import CSlash.Types.Basic hiding( SuccessFlag(..) )
-- import GHC.Types.Annotations
import CSlash.Types.SrcLoc
import CSlash.Types.SourceFile
import CSlash.Types.PkgQual
-- import qualified GHC.LanguageExtensions as LangExt

import CSlash.Unit.External
import CSlash.Unit.Types
import CSlash.Unit.State
import CSlash.Unit.Home
import CSlash.Unit.Module
import CSlash.Unit.Module.Warnings
import CSlash.Unit.Module.ModSummary
import CSlash.Unit.Module.ModIface
import CSlash.Unit.Module.ModDetails
import CSlash.Unit.Module.Deps

import CSlash.Data.FastString
import CSlash.Data.Maybe
import CSlash.Data.List.SetOps
import CSlash.Data.Bag
-- import qualified GHC.Data.BooleanFormula as BF

import Control.Arrow ( second )
import Control.DeepSeq
import Control.Monad
import Control.Monad.Trans.Writer.CPS
import Data.Data ( Data )
import Data.Functor.Classes ( liftEq )
import Data.List ( sortBy, sort )
import Data.List.NonEmpty ( NonEmpty (..) )
import qualified Data.List.NonEmpty as NE
import Data.Ord
import qualified Data.Set as S
import Data.Foldable ( for_ )
import Data.Traversable ( for )

type RenamedStuff =
  Maybe ( CsGroup Rn
        , [LImportDecl Rn]
        , Maybe [(LIE Rn, Avails)]
        , Maybe (XRec Rn ModuleName)
        )
