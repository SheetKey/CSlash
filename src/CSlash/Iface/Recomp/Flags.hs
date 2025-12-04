{-# LANGUAGE RecordWildCards #-}

module CSlash.Iface.Recomp.Flags where

import CSlash.Driver.Session
import CSlash.Driver.Env

import CSlash.Utils.Binary
import CSlash.Unit.Module
import CSlash.Types.Name
-- import GHC.Types.SafeHaskell
import CSlash.Utils.Fingerprint
import CSlash.Iface.Recomp.Binary
import CSlash.Core.Opt.CallerCC ()

import CSlash.Data.EnumSet as EnumSet
import System.FilePath (normalise)

import Debug.Trace (trace)

fingerprintDynFlags :: CsEnv -> Module -> (WriteBinHandle -> Name -> IO ()) -> IO Fingerprint
fingerprintDynFlags cs_env this_mod nameio =
  let dflags@DynFlags{..} = cs_dflags cs_env
      mainis = if mainModIs (cs_HUE cs_env) == this_mod then Just mainFunIs else Nothing

      includePathsMinusImplicit = includePaths { includePathsQuoteImplicit = [] }

      flags = (mainis, (debugLevel, callerCcFilters))
  in computeFingerprint nameio flags

fingerprintOptFlags :: DynFlags -> (WriteBinHandle -> Name -> IO ()) -> IO Fingerprint
fingerprintOptFlags DynFlags{..} nameio =
  let opt_flags = map fromEnum $ filter (`EnumSet.member` optimisationFlags)
                                        (EnumSet.toList generalFlags)
  in computeFingerprint nameio opt_flags

fingerprintPcFlags :: DynFlags -> (WriteBinHandle -> Name -> IO ()) -> IO Fingerprint
fingerprintPcFlags dflags@DynFlags{..} nameio =
  let pc = if gopt Opt_Pc dflags then Just pcDir else Nothing
  in computeFingerprint nameio pc
