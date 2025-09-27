{-# LANGUAGE TupleSections #-}

module CSlash.Tc.Utils.Env
  ( TyThing (..), TcTyKiThing(..)
  , module CSlash.Tc.Utils.Env
  ) where

import CSlash.Driver.Env
import CSlash.Driver.Env.KnotVars
import CSlash.Driver.DynFlags

import CSlash.Builtin.Names
import CSlash.Builtin.Types

-- import GHC.Runtime.Context

import CSlash.Cs

import CSlash.Iface.Env
import CSlash.Iface.Load

import CSlash.Tc.Errors.Types
import CSlash.Tc.Utils.Monad
import CSlash.Tc.Utils.TcType
import {-# SOURCE #-} CSlash.Tc.Utils.TcMType ( tcCheckUsage )
import CSlash.Tc.Types.LclEnv
import CSlash.Tc.Types.BasicTypes
import CSlash.Tc.Types.Evidence (AnyCsWrapper, idCsWrapper, (<.>))

-- import GHC.Core.InstEnv
import CSlash.Core.DataCon ( DataCon, dataConTyCon{-, flSelector-} )
-- import GHC.Core.PatSyn  ( PatSyn )
import CSlash.Core.ConLike
import CSlash.Core.TyCon
import CSlash.Core.Type.Rep
import CSlash.Core.Type
import CSlash.Core.Type.FVs
import CSlash.Core.Kind
import CSlash.Core.UsageEnv
-- import GHC.Core.Coercion.Axiom
-- import GHC.Core.Class

import CSlash.Unit.Module
import CSlash.Unit.Home
import CSlash.Unit.External

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Encoding
import CSlash.Utils.Misc ( HasDebugCallStack )

import CSlash.Data.FastString
import CSlash.Data.Bag
import CSlash.Data.List.SetOps
import CSlash.Data.Maybe( MaybeErr(..), orElse )

import CSlash.Types.SrcLoc
import CSlash.Types.Basic hiding( SuccessFlag(..) )
import CSlash.Types.TypeEnv
import CSlash.Types.SourceFile
import CSlash.Types.Name hiding (varName)
import CSlash.Types.Name.Set
import CSlash.Types.Name.Env
import CSlash.Types.Id
import CSlash.Types.Var (AnyTyVar, KiVar, AnyKiVar, asAnyTyKi, varType, varName)
-- import CSlash.Types.Id.Info ( RecSelParent(..) )
import CSlash.Types.Name.Reader
import CSlash.Types.TyThing
import CSlash.Types.Unique.Set ( nonDetEltsUniqSet )

import Data.IORef
import Data.List          ( intercalate )
import Control.Monad
import CSlash.Iface.Errors.Types
import CSlash.Types.Error

{- *********************************************************************
*                                                                      *
            An IO interface to looking up globals
*                                                                      *
********************************************************************* -}

addTypecheckedBinds :: TcGblEnv p -> [LCsBinds p] -> TcGblEnv p
addTypecheckedBinds tcg_env binds
  = tcg_env { tcg_binds = foldr (++) (tcg_binds tcg_env) binds }

{- *********************************************************************
*                                                                      *
            tcLookupGlobal
*                                                                      *
********************************************************************* -}

tcLookupGlobal :: Name -> TcM WITyThing
tcLookupGlobal name = do
  env <- getGblEnv
  case lookupNameEnv (tcg_type_env env) name of
    Just thing -> return thing
    Nothing -> if nameIsLocalOrFrom (tcg_mod env) name
               then notFound name
               else do mb_thing <- tcLookupImported_maybe name
                       case mb_thing of
                         Succeeded thing -> return thing
                         Failed msg -> failWithTc (TcRnInterfaceError msg)

tcLookupGlobalOnly :: Name -> TcM WITyThing
tcLookupGlobalOnly name = do
  env <- getGblEnv
  return $ case lookupNameEnv (tcg_type_env env) name of
             Just thing -> thing
             Nothing -> pprPanic "tcLookupGlobalOnly" (ppr name)

tcLookupTyCon :: Name -> TcM (TyCon (TyVar KiVar) KiVar)
tcLookupTyCon name = do
  thing <- tcLookupGlobal name
  case thing of
    ATyCon tc -> return tc
    _ -> wrongThingErr WrongThingTyCon (AGlobal $ asAnyTyKi thing) name

{- *********************************************************************
*                                                                      *
                Extending the global environment
*                                                                      *
********************************************************************* -}

setGlobalTypeEnv :: TcGblEnv p -> TypeEnv -> TcM (TcGblEnv p)
setGlobalTypeEnv tcg_env new_type_env = do
  case lookupKnotVars (tcg_type_env_var tcg_env) (tcg_mod tcg_env) of
    Just tcg_env_var -> writeMutVar tcg_env_var new_type_env
    Nothing -> return ()
  return $ tcg_env { tcg_type_env = new_type_env }

tcExtendGlobalEnvImplicit :: [WITyThing] -> TcM r -> TcM r
tcExtendGlobalEnvImplicit things thing_inside = do
  tcg_env <- getGblEnv
  let ge' = extendTypeEnvList (tcg_type_env tcg_env) things
  tcg_env' <- setGlobalTypeEnv tcg_env ge'
  setGblEnv tcg_env' thing_inside

tcExtendTyConEnv :: [TyCon (TyVar KiVar) KiVar] -> TcM r -> TcM r
tcExtendTyConEnv tycons thing_inside = do
  env <- getGblEnv
  let env' = env { tcg_tcs = tycons ++ tcg_tcs env }
  setGblEnv env' $ tcExtendGlobalEnvImplicit (map ATyCon tycons) thing_inside

tcExtendRecEnv :: [(Name, WITyThing)] -> TcM r -> TcM r
tcExtendRecEnv gbl_stuff thing_inside = do
  tcg_env <- getGblEnv
  let ge' = extendNameEnvList (tcg_type_env tcg_env) gbl_stuff
      tcg_env' = tcg_env { tcg_type_env = ge' }
  setGblEnv tcg_env' thing_inside

{- *********************************************************************
*                                                                      *
            The local environment
*                                                                      *
********************************************************************* -}

tcLookup :: Name -> TcM TcTyKiThing
tcLookup name = do
  local_env <- getLclTyKiEnv
  case lookupNameEnv local_env name of
    Just thing -> return thing
    Nothing -> (AGlobal . asAnyTyKi) <$> tcLookupGlobal name

tcLookupId :: Name -> TcM AnyId
tcLookupId name = do
  thing <- tcLookupIdMaybe name
  case thing of
    Just id -> return id
    _ -> pprPanic "tcLookupId" (ppr name)

tcLookupIdMaybe :: Name -> TcM (Maybe AnyId)
tcLookupIdMaybe name = do
  thing <- tcLookup name
  case thing of
    ATcId { tct_id = id } -> return $ Just $ asAnyTyKi id
    AGlobal (AnId id) -> return $ Just $ asAnyTyKi id
    _ -> return Nothing

tcLookupTcTyCon :: HasDebugCallStack => Name -> TcM AnyTyCon
tcLookupTcTyCon name = do
  thing <- tcLookup name
  case thing of
    ATcTyCon tc -> return tc
    _ -> pprPanic "tcLookupTcTyCon" (ppr name)

tcExtendKindEnvList :: [(Name, TcTyKiThing)] -> TcM r -> TcM r
tcExtendKindEnvList things thing_inside = do
  traceTc "tcExtendKindEnvList" (ppr things)
  updLclCtxt upd_env thing_inside
  where
    upd_env env = env { tcl_env = extendNameEnvList (tcl_env env) things }

tcExtendKiVarEnv :: [AnyKiVar] -> TcM r -> TcM r
tcExtendKiVarEnv kvs thing_inside = tcExtendNameKiVarEnv (mkVarNamePairs kvs) thing_inside

tcExtendNameTyVarEnv :: [(Name, AnyTyVar AnyKiVar)] -> TcM r -> TcM r
tcExtendNameTyVarEnv binds thing_inside
  = tc_extend_local_env NotTopLevel names
    $ tcExtendBinderStack tv_binds
    $ thing_inside
  where
    tv_binds = [TcTvBndr name tv | (name, tv) <- binds]
    names = [(name, ATyVar name tv) | (name, tv) <- binds]

tcExtendNameKiVarEnv :: [(Name, AnyKiVar)] -> TcM r -> TcM r
tcExtendNameKiVarEnv binds thing_inside
  = tc_extend_local_env NotTopLevel names
    $ tcExtendBinderStack kv_binds
    $ thing_inside
  where
    kv_binds = [TcKvBndr name kv | (name, kv) <- binds]
    names = [(name, AKiVar name kv) | (name, kv) <- binds]

isTypeClosedLetBndr :: TcId -> Bool
isTypeClosedLetBndr = noFreeVarsOfType . varType

tcExtendSigIds :: TopLevelFlag -> [TcId] -> TcM a -> TcM a
tcExtendSigIds top_lvl sig_ids thing_inside
  = tc_extend_local_env top_lvl
    [ (idName id, ATcId id info)
    | id <- sig_ids
    , let closed = isTypeClosedLetBndr id
          info = NonClosedLet emptyNameSet closed ]
    thing_inside

tcExtendLetEnv
  :: TopLevelFlag
  -> TcSigFun
  -> IsGroupClosed
  -> [TcId]
  -> TcM a
  -> TcM (a, AnyCsWrapper)
tcExtendLetEnv top_lvl sig_fn (IsGroupClosed fvs fv_type_closed) ids thing_inside
  = tcExtendBinderStack [TcIdBndr id top_lvl | id <- ids]
    $ tc_extend_local_env top_lvl
      [ (varName id, ATcId { tct_id = id, tct_info = mk_tct_info id })
      | id <- ids ]
    $ foldr check_usage ((, idCsWrapper) <$> thing_inside) ids
  where
    mk_tct_info id
      | type_closed && isEmptyNameSet rhs_fvs = ClosedLet
      | otherwise = NonClosedLet rhs_fvs type_closed
      where
        name = varName id
        rhs_fvs = lookupNameEnv fvs name `orElse` emptyNameSet
        type_closed = isTypeClosedLetBndr id
                      && (fv_type_closed || hasCompleteSig sig_fn name)

    check_usage :: TcId -> TcM (a, AnyCsWrapper) -> TcM (a, AnyCsWrapper)
    check_usage id thing_inside = do
      ((res, inner_wrap), outer_wrap) <- tcCheckUsage (varName id) (idKind id) thing_inside
      return (res, outer_wrap <.> inner_wrap)

tcExtendIdEnv1 :: Name -> TcId -> TcM a -> TcM a
tcExtendIdEnv1 name id thing_inside = tcExtendIdEnv2 [(name, id)] thing_inside

tcExtendIdEnv2 :: [(Name, TcId)] -> TcM a -> TcM a
tcExtendIdEnv2 names_w_ids thing_inside
  = tcExtendBinderStack [ TcIdBndr mono_id NotTopLevel
                        | (_, mono_id) <- names_w_ids ]
    $ tc_extend_local_env NotTopLevel [ (name, ATcId { tct_id = id, tct_info = NotLetBound })
                                      | (name, id) <- names_w_ids ]
    thing_inside
    

tc_extend_local_env :: TopLevelFlag -> [(Name, TcTyKiThing)] -> TcM a -> TcM a
tc_extend_local_env top_lvl extra_env thing_inside = do
  traceTc "tc_extend_local_env" (ppr extra_env)
  updLclCtxt upd_lcl_env thing_inside
  where
    upd_lcl_env env0@(TcLclCtxt { tcl_rdr = rdr_env, tcl_env = lcl_type_env })
      = env0 { tcl_rdr = extendLocalRdrEnvList rdr_env
                         [ n | (n, _) <- extra_env, isInternalName n ]
             , tcl_env = extendNameEnvList lcl_type_env extra_env }

{- *********************************************************************
*                                                                      *
             TcBinderStack
*                                                                      *
********************************************************************* -}

tcExtendBinderStack :: [TcBinder] -> TcM a -> TcM a
tcExtendBinderStack bndrs thing_inside = do
  traceTc "tcExtendBinderStack" (ppr bndrs)
  updLclCtxt (\env -> env { tcl_bndrs = bndrs ++ tcl_bndrs env }) thing_inside

{- *********************************************************************
*                                                                      *
             Adding placeholders
*                                                                      *
********************************************************************* -}

getTypeSigNames :: [LSig Rn] -> NameSet
getTypeSigNames sigs = foldr get_type_sig emptyNameSet sigs
  where
    get_type_sig sig ns = case sig of
      L _ (TypeSig _ name _) -> extendNameSet ns (unLoc name)
      _ -> ns

{- *********************************************************************
*                                                                      *
                Errors
*                                                                      *
********************************************************************* -}

notFound :: Name -> TcM WITyThing
notFound name = do
  lcl_env <- getLclEnv
  if isTermVarNameSpace (nameNameSpace name)
    then failWithTc $ panic "TcRnUnpromotableThing name TermVariablePE"
    else failWithTc $ 
         mkTcRnNotInScope (getRdrName name) (NotInScopeTc (getLclEnvTypeEnv lcl_env))

wrongThingErr :: WrongThingSort -> TcTyKiThing -> Name -> TcM a
wrongThingErr expected thing name = failWithTc (TcRnTyThingUsedWrong expected thing name)
