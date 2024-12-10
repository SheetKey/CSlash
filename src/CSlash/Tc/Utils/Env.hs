module CSlash.Tc.Utils.Env where

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
-- import {-# SOURCE #-} GHC.Tc.Utils.TcMType ( tcCheckUsage )
import CSlash.Tc.Types.LclEnv
-- import GHC.Tc.Types.Evidence (HsWrapper, idHsWrapper, (<.>))

-- import GHC.Core.InstEnv
import CSlash.Core.DataCon ( DataCon, dataConTyCon{-, flSelector-} )
-- import GHC.Core.PatSyn  ( PatSyn )
import CSlash.Core.ConLike
import CSlash.Core.TyCon
import CSlash.Core.Type.Rep
import CSlash.Core.Type
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
import CSlash.Types.Name
import CSlash.Types.Name.Set
import CSlash.Types.Name.Env
import CSlash.Types.Id
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
            tcLookupGlobal
*                                                                      *
********************************************************************* -}

tcLookupGlobal :: Name -> TcM TyThing
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

{- *********************************************************************
*                                                                      *
            The local environment
*                                                                      *
********************************************************************* -}

tcLookup :: Name -> TcM TcTyThing
tcLookup name = do
  local_env <- getLclTypeEnv
  case lookupNameEnv local_env name of
    Just thing -> return thing
    Nothing -> AGlobal <$> tcLookupGlobal name

tcLookupTcTyCon :: HasDebugCallStack => Name -> TcM TcTyCon
tcLookupTcTyCon name = do
  thing <- tcLookup name
  case thing of
    ATcTyCon tc -> return tc
    _ -> pprPanic "tcLookupTcTyCon" (ppr name)

tcExtendKindEnvList :: [(Name, TcTyThing)] -> TcM r -> TcM r
tcExtendKindEnvList things thing_inside = do
  traceTc "tcExtendKindEnvList" (ppr things)
  updLclCtxt upd_env thing_inside
  where
    upd_env env = env { tcl_env = extendNameEnvList (tcl_env env) things }

tcExtendNameKiVarEnv :: [(Name, TcKiVar)] -> TcM r -> TcM r
tcExtendNameKiVarEnv binds thing_inside
  = tc_extend_local_env NotTopLevel names
    $ tcExtendBinderStack kv_binds
    $ thing_inside
  where
    kv_binds = [TcKvBndr name kv | (name, kv) <- binds]
    names = [(name, AKiVar name kv) | (name, kv) <- binds]

tc_extend_local_env :: TopLevelFlag -> [(Name, TcTyThing)] -> TcM a -> TcM a
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

notFound :: Name -> TcM TyThing
notFound name = do
  lcl_env <- getLclEnv
  if isTermVarNameSpace (nameNameSpace name)
    then failWithTc $ panic "TcRnUnpromotableThing name TermVariablePE"
    else failWithTc $ 
         mkTcRnNotInScope (getRdrName name) (NotInScopeTc (getLclEnvTypeEnv lcl_env))

wrongThingErr :: WrongThingSort -> TcTyThing -> Name -> TcM a
wrongThingErr expected thing name = panic "failWithTc (TcRnTyThingUsedWrong expected thing name)"
