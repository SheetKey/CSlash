module CSlash.Tc.Validity where

import CSlash.Data.FastString

import CSlash.Data.Maybe

-- friends:
-- import GHC.Tc.Utils.Unify    ( tcSubTypeAmbiguity )
-- import GHC.Tc.Solver         ( simplifyAmbiguityCheck )
-- import GHC.Tc.Instance.Class ( matchGlobalInst, ClsInstResult(..), AssocInstInfo(..) )
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Types.Origin
-- import GHC.Tc.Types.Rank
import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
-- import GHC.Tc.Instance.FunDeps
-- import GHC.Tc.Instance.Family
import CSlash.Tc.Zonk.TcType

import CSlash.Builtin.Types
import CSlash.Builtin.Names
import CSlash.Builtin.Uniques  ( mkAlphaTyVarUnique )

import CSlash.Core.Type
import CSlash.Core.Kind
-- import GHC.Core.Unify ( typesAreApart, tcMatchTyX_BM, BindFlag(..) )
-- import GHC.Core.Coercion
-- import GHC.Core.Coercion.Axiom
-- import GHC.Core.Class
import CSlash.Core.TyCon
-- import GHC.Core.Predicate
import CSlash.Core.Type.FVs
import CSlash.Core.Type.Rep
import CSlash.Core.Type.Ppr
-- import GHC.Core.FamInstEnv ( isDominatedBy, injectiveBranches
--                            , InjectivityCheckResult(..) )

import CSlash.Cs
import CSlash.Driver.Session

import CSlash.Types.Error
import CSlash.Types.Basic   ( TypeOrKind(..) )
import CSlash.Types.Name
import CSlash.Types.Var.Env
import CSlash.Types.Var.Set
import CSlash.Types.Var     ( VarBndr(..){-, isInvisibleFunArg-}, mkTyVar, tyVarName )
import CSlash.Types.SourceFile
import CSlash.Types.SrcLoc
import CSlash.Types.TyThing ( TyThing(..) )
import CSlash.Types.Unique.Set( isEmptyUniqSet )

-- import CSlash.Utils.FV
import CSlash.Utils.Error
import CSlash.Utils.Misc
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Panic

import CSlash.Data.List.SetOps

import Control.Monad
import Data.Foldable
import Data.Function
import Data.List        ( (\\) )
import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty ( NonEmpty(..) )

{- *********************************************************************
*                                                                      *
          Checking validity of a kind
*                                                                      *
********************************************************************* -}

checkValidKind :: UserTypeCtxt -> Kind -> TcM ()
checkValidKind _ctxt ki = traceTc "checkValidKind" (ppr ki)
