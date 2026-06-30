module CSlash.StgToPir.CgUtils
  ( CgStream
  ) where

-- import CSlash.Platform.Regs
import CSlash.Platform
-- import GHC.Cmm
-- import GHC.Cmm.Dataflow.Block
-- import GHC.Cmm.Dataflow.Graph
-- import GHC.Cmm.Utils
-- import GHC.Cmm.CLabel
-- import GHC.Cmm.Dataflow.Label

import CSlash.Utils.Panic
import CSlash.Data.Stream (Stream)
import CSlash.Types.Unique.DSM (UniqDSMT)

type CgStream = Stream (UniqDSMT IO)
