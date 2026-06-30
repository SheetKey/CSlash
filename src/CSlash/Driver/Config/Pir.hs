module CSlash.Driver.Config.Pir (initPirConfig) where

import CSlash.Pir.Config

import CSlash.Driver.DynFlags
import CSlash.Driver.Backend

import CSlash.Platform

initPirConfig :: DynFlags -> PirConfig
initPirConfig dflags = PirConfig
  { pirProfile = targetProfile dflags
  , pirOptControlFlow = gopt Opt_PirControlFlow dflags
  , pirDoLinting = gopt Opt_DoPirLinting dflags
  , pirOptElimCommonBlks = gopt Opt_PirElimCommonBlocks dflags
  , pirExternalDynamicRefs = gopt Opt_ExternalDynamicRefs dflags
  }
