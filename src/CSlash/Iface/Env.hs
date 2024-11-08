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

{- *****************************************************
*                                                      *
        Allocating new Names in the Name Cache
*                                                      *
***************************************************** -}

newGlobalBinder :: Module -> OccName -> SrcSpan -> TcRnIf a b Name
newGlobalBinder mod occ loc = do
  cs_env <- getTopEnv
  name <- liftIO $ allocateGlobalBinder (cs_NC cs_env) mod occ loc
  traceIf $ text "newGlobalBinder" <+> (vcat [ ppr mod <+> ppr occ <+> ppr loc, ppr name ])
  return name

allocateGlobalBinder :: NameCache -> Module -> OccName -> SrcSpan -> IO Name
allocateGlobalBinder nc mod occ loc = updateNameCache nc mod occ $ \cache0 -> 
  case lookupOrigNameCache cache0 mod occ of
    Just name | isWiredInName name
                -> pure (cache0, name)
              | otherwise
                -> pure (new_cache, name')
              where
                uniq = nameUnique name
                name' = mkExternalName uniq mod occ loc
                new_cache = extendOrigNameCache cache0 mod occ name'
    Nothing -> do uniq <- takeUniqFromNameCache nc
                  let name = mkExternalName uniq mod occ loc
                      new_cache = extendOrigNameCache cache0 mod occ name
                  pure (new_cache, name)

{- *********************************************************************
*                                                                      *
                Name cache access
*                                                                      *
********************************************************************* -}

externalizeName :: Module -> Name -> TcRnIf m n Name
externalizeName mod name = do
  let occ = nameOccName name
      loc = nameSrcSpan name
      uniq = nameUnique name
  occ `seq` return ()
  cs_env <- getTopEnv
  liftIO $ updateNameCache (cs_NC cs_env) mod occ $ \cache -> 
    let name' = mkExternalName uniq mod occ loc
        cache' = extendOrigNameCache cache mod occ name'
    in pure (cache', name')

{- *********************************************************************
*                                                                      *
                Tracing
*                                                                      *
********************************************************************* -}

trace_if :: Logger -> SDoc -> IO ()
{-# INLINE trace_if #-}
trace_if logger doc = when (logHasDumpFlag logger Opt_D_dump_if_trace) $ putMsg logger doc

trace_hi_diffs :: Logger -> SDoc -> IO ()
{-# INLINE trace_hi_diffs #-}
trace_hi_diffs logger doc = when (logHasDumpFlag logger Opt_D_dump_hi_diffs) $ putMsg logger doc
