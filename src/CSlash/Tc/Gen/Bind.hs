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
import CSlash.Tc.Gen.Sig
-- import GHC.Tc.Utils.Concrete ( hasFixedRuntimeRep_syntactic )
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Types.Origin
import CSlash.Tc.Types.BasicTypes
import CSlash.Tc.Utils.Env
-- import GHC.Tc.Utils.Unify
import CSlash.Tc.Solver
import CSlash.Tc.Types.Evidence
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
tcTopBinds binds sigs = do
  (binds', wrap, (tcg_env, tcl_env)) <- tcValBinds TopLevel binds sigs getEnvs

  panic "unfinished1"


tcValBinds
  :: TopLevelFlag
  -> [(RecFlag, LCsBinds Rn)]
  -> [LSig Rn]
  -> TcM thing
  -> TcM ([(RecFlag, LCsBinds Tc)], CsWrapper, thing)
tcValBinds top_lvl binds sigs thing_inside = do
  (poly_ids, sig_fn) <- tcTySigs sigs

  tcExtendSigIds top_lvl poly_ids $ 
    tcBindGroups top_lvl sig_fn binds thing_inside
             
tcBindGroups
  :: TopLevelFlag
  -> TcSigFun
  -> [(RecFlag, LCsBinds Rn)]
  -> TcM thing
  -> TcM ([(RecFlag, LCsBinds Tc)], CsWrapper, thing)
tcBindGroups _ _ [] thing_inside = do
  thing <- thing_inside
  return ([], idCsWrapper, thing)

tcBindGroups top_lvl sig_fn (group:groups) thing_inside = do
  type_env <- getLclTyKiEnv
  let closed = isClosedBndrGroup type_env (snd group)
  (group', outer_wrapper, (groups', inner_wrapper, thing))
    <- tc_group top_lvl sig_fn group closed
       $ tcBindGroups top_lvl sig_fn groups thing_inside
  return (group' ++ groups', outer_wrapper <.> inner_wrapper, thing)

tc_group
  :: TopLevelFlag
  -> TcSigFun
  -> (RecFlag, LCsBinds Rn)
  -> IsGroupClosed
  -> TcM thing
  -> TcM ([(RecFlag, LCsBinds Tc)], CsWrapper, thing)
tc_group = panic "unfinished2"

{- *********************************************************************
*                                                                      *
                Generalisation
*                                                                      *
********************************************************************* -}

isClosedBndrGroup :: TcTyKiEnv -> Bag (LCsBind Rn) -> IsGroupClosed
isClosedBndrGroup type_env binds = IsGroupClosed fv_env type_closed
  where
    type_closed = allUFM (nameSetAll is_closed_type_id) fv_env

    fv_env :: NameEnv NameSet
    fv_env = mkNameEnv $ concatMap (bindFvs . unLoc) binds

    bindFvs :: CsBindLR Rn Rn -> [(Name, NameSet)]
    bindFvs (FunBind { fun_id = L _ f, fun_ext = fvs })
      = let open_fvs = get_open_fvs fvs
        in [(f, open_fvs)]
    bindFvs _ = panic "bindFvs"

    get_open_fvs fvs = filterNameSet (not . is_closed) fvs

    is_closed :: Name -> ClosedTypeId
    is_closed name
      | Just thing <- lookupNameEnv type_env name
      = case thing of
          AGlobal {} -> True
          ATcId { tct_info = ClosedLet } -> True
          _ -> False

      | otherwise
      = True

    is_closed_type_id :: Name -> ClosedTypeId
    is_closed_type_id name
      | Just thing <- lookupNameEnv type_env name
      = case thing of
          ATcId { tct_info = NonClosedLet _ cl } -> cl
          ATcId { tct_info = NotLetBound } -> False
          ATyVar {} -> False
          AKiVar {} -> False
          _ -> pprPanic "is_closed_id" (ppr name)

      | otherwise
      = True
