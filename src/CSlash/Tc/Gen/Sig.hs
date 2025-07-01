module CSlash.Tc.Gen.Sig where

import CSlash.Data.FastString

import CSlash.Driver.DynFlags
import CSlash.Driver.Backend

import CSlash.Cs

import CSlash.Tc.Errors.Types ( TcRnMessage(..) )
import CSlash.Tc.Gen.CsType
import CSlash.Tc.Types
import CSlash.Tc.Solver( pushLevelAndSolveX, reportUnsolved' )
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Zonk.Type
import CSlash.Tc.Types.Origin
import CSlash.Tc.Utils.TcType
import CSlash.Tc.Validity ( checkValidType )
import CSlash.Tc.Utils.Unify( tcSkolemise, unifyType )
-- import CSlash.Tc.Utils.Instantiate( topInstantiate, tcInstTypeBndrs )
import CSlash.Tc.Utils.Env( tcLookupId )
import CSlash.Tc.Types.Evidence( HsWrapper, (<.>) )

-- import CSlash.Core( hasSomeUnfolding )
-- import CSlash.Core.Type ( mkTyVarBinders )
import CSlash.Core.Kind
-- import CSlash.Core.Type.Rep( mkNakedFunTy )

import CSlash.Types.Var ( TyVar, Specificity(..), tyVarKind, binderVars, invisArgTypeLike )
import CSlash.Types.Id  ( Id, idName, idType, setInlinePragma
                        , mkLocalId, realIdUnfolding )
import CSlash.Types.Basic
import CSlash.Types.Name
import CSlash.Types.Name.Env
import CSlash.Types.SrcLoc

import CSlash.Builtin.Names( mkUnboundName )
import CSlash.Unit.Module( getModule )

import CSlash.Utils.Misc as Utils ( singleton )
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import CSlash.Data.Maybe( orElse, whenIsJust )

import Data.Maybe( mapMaybe )
import qualified Data.List.NonEmpty as NE
import Control.Monad( unless )

{- *********************************************************************
*                                                                      *
               Typechecking user signatures
*                                                                      *
********************************************************************* -}

tcTySigs :: [LSig Rn] -> TcM ([TcId], TcSigFun)
tcTySigs cs_sigs = checkNoErrs $ do
  ty_sigs_s <- mapAndReportM tcTySig cs_sigs

  panic "unfinished3"

tcTySig :: LSig Rn -> TcM [TcSigInfo]
tcTySig = panic "unfinished4"
