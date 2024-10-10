module CSlash.Iface.Env where

import CSlash.Driver.Env
import CSlash.Driver.DynFlags

import CSlash.Tc.Utils.Monad
import CSlash.Core.Type
import CSlash.Iface.Type
-- import GHC.Runtime.Context

import CSlash.Unit.Module
import CSlash.Unit.Module.ModIface

import CSlash.Data.FastString
import CSlash.Data.FastString.Env

import CSlash.Types.Var
import CSlash.Types.Name
import CSlash.Types.Avail
import CSlash.Types.Name.Cache
import CSlash.Types.Unique.Supply
import CSlash.Types.SrcLoc

import CSlash.Utils.Outputable
import CSlash.Utils.Error
import CSlash.Utils.Logger

import Data.List     ( partition )
import Control.Monad

{- *********************************************************************
*                                                                      *
                Tracing
*                                                                      *
********************************************************************* -}

trace_if :: Logger -> SDoc -> IO ()
{-# INLINE trace_if #-}
trace_if logger doc = when (logHasDumpFlag logger Opt_D_dump_if_trace) $ putMsg logger doc
