{-# LANGUAGE BangPatterns #-}

module CSlash.Tc.Types.LclEnv where

import CSlash.Tc.Utils.TcType ( TcLevel )
import CSlash.Tc.Errors.Types ( TcRnMessage )

import CSlash.Core.UsageEnv ( UsageEnv )

import CSlash.Types.Name.Reader ( LocalRdrEnv )
import CSlash.Types.Name.Env ( NameEnv )
import CSlash.Types.SrcLoc ( RealSrcSpan )
import CSlash.Types.Basic ( TopLevelFlag )

import CSlash.Types.Error ( Messages )

import CSlash.Tc.Types.BasicTypes
import CSlash.Tc.Types.TcRef
import CSlash.Tc.Types.ErrCtxt
import CSlash.Tc.Types.Constraint ( WantedConstraints )

{- *********************************************************************
*                                                                      *
                The local typechecker environment
*                                                                      *
********************************************************************* -}

data TcLclEnv = TcLclEnv
  { tcl_lcl_ctxt :: !TcLclCtxt
  , tcl_usage :: TcRef UsageEnv
  , tcl_lie :: TcRef WantedConstraints
  , tcl_errs :: TcRef (Messages TcRnMessage)
  }

data TcLclCtxt = TcLclCtxt
  { tcl_loc :: RealSrcSpan
  , tcl_ctxt :: [ErrCtxt]
  , tcl_tclvl :: TcLevel
  , tcl_bndrs :: TcBinderStack
  , tcl_rdr :: LocalRdrEnv
  , tcl_env :: TcTypeEnv
  }

getLclEnvTypeEnv :: TcLclEnv -> TcTypeEnv
getLclEnvTypeEnv = tcl_env . tcl_lcl_ctxt

setLclEnvTypeEnv :: TcTypeEnv -> TcLclEnv -> TcLclEnv
setLclEnvTypeEnv ty_env = modifyLclCtxt (\env -> env { tcl_env = ty_env})

setLclEnvTcLevel :: TcLevel -> TcLclEnv -> TcLclEnv
setLclEnvTcLevel lvl = modifyLclCtxt (\env -> env {tcl_tclvl = lvl })

modifyLclEnvTcLevel :: (TcLevel -> TcLevel) -> TcLclEnv -> TcLclEnv
modifyLclEnvTcLevel f = modifyLclCtxt (\env -> env { tcl_tclvl = f (tcl_tclvl env)})

getLclEnvTcLevel :: TcLclEnv -> TcLevel
getLclEnvTcLevel = tcl_tclvl . tcl_lcl_ctxt

setLclEnvLoc :: RealSrcSpan -> TcLclEnv -> TcLclEnv
setLclEnvLoc loc = modifyLclCtxt (\lenv -> lenv { tcl_loc = loc })

getLclEnvLoc :: TcLclEnv -> RealSrcSpan
getLclEnvLoc = tcl_loc . tcl_lcl_ctxt

getLclEnvErrCtxt :: TcLclEnv -> [ErrCtxt]
getLclEnvErrCtxt = tcl_ctxt . tcl_lcl_ctxt

setLclEnvErrCtxt :: [ErrCtxt] -> TcLclEnv -> TcLclEnv
setLclEnvErrCtxt ctxt = modifyLclCtxt (\env -> env { tcl_ctxt = ctxt })

addLclEnvErrCtxt :: ErrCtxt -> TcLclEnv -> TcLclEnv
addLclEnvErrCtxt ctxt = modifyLclCtxt (\env -> env { tcl_ctxt = ctxt : (tcl_ctxt env) })

getLclEnvBinderStack :: TcLclEnv -> TcBinderStack
getLclEnvBinderStack = tcl_bndrs . tcl_lcl_ctxt

setLclEnvBinderStack :: TcBinderStack -> TcLclEnv -> TcLclEnv
setLclEnvBinderStack stack = modifyLclCtxt (\env -> env { tcl_bndrs = stack })

getLclEnvRdrEnv :: TcLclEnv -> LocalRdrEnv
getLclEnvRdrEnv = tcl_rdr . tcl_lcl_ctxt

setLclEnvRdrEnv :: LocalRdrEnv -> TcLclEnv -> TcLclEnv
setLclEnvRdrEnv rdr_env = modifyLclCtxt (\env -> env { tcl_rdr = rdr_env })

modifyLclCtxt :: (TcLclCtxt -> TcLclCtxt) -> TcLclEnv -> TcLclEnv
modifyLclCtxt upd env =
  let !res = upd (tcl_lcl_ctxt env)
  in env { tcl_lcl_ctxt = res }

type TcTypeEnv = NameEnv TcTyThing

