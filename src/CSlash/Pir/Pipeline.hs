module CSlash.Pir.Pipeline (pirPipeline) where

import CSlash.Driver.Flags

import CSlash.Pir
import CSlash.Pir.Config
-- import GHC.Cmm.ContFlowOpt
-- import GHC.Cmm.CommonBlockElim
import CSlash.Pir.Dataflow.Label
-- import GHC.Cmm.Info.Build
-- import GHC.Cmm.Lint
-- import GHC.Cmm.LayoutStack
-- import GHC.Cmm.ProcPoint
-- import GHC.Cmm.Sink
-- import GHC.Cmm.Switch.Implement
-- import GHC.Cmm.ThreadSanitizer

import CSlash.Types.Unique.Supply
import CSlash.Types.Unique.DSM

import CSlash.Utils.Error
import CSlash.Utils.Logger
import CSlash.Utils.Outputable
import CSlash.Utils.Misc ( partitionWith )
import CSlash.Utils.Panic

import CSlash.Platform

import Control.Monad
import CSlash.Utils.Monad (mapAccumLM)

pirPipeline
  :: Logger
  -> PirConfig
  -> PirGroup
  -> DUniqSupply
  -> IO (RawPirGroup, DUniqSupply)
pirPipeline logger pir_config dus0 = panic "pirPipeline"
