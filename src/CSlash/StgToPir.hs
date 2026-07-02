module CSlash.StgToPir (codeGen) where

import CSlash.Pir.UniqueRenamer
-- import CSlash.StgToPir.Prof (initCostCentres, ldvEnter)
import CSlash.StgToPir.Monad
-- import CSlash.StgToPir.Env
-- import CSlash.StgToPir.Bind
-- import CSlash.StgToPir.DataCon
-- import CSlash.StgToPir.Layout
-- import CSlash.StgToPir.Utils
-- import CSlash.StgToPir.Closure
import CSlash.StgToPir.Config
-- import CSlash.StgToPir.Ticky
-- import CSlash.StgToPir.Types (ModuleLFInfos)
import CSlash.StgToPir.CgUtils (CgStream)

import CSlash.Pir
-- import CSlash.Pir.Utils
import CSlash.Pir.PLabel
import CSlash.Pir.Graph

import CSlash.Stg.Syntax

-- import GHC.Types.CostCentre
-- import GHC.Types.IPE
import CSlash.Types.Var.Id
import CSlash.Types.Var.Id.Info
import CSlash.Types.RepType
import CSlash.Types.Basic
import CSlash.Types.Var.Set ( isEmptyDVarSet )
import CSlash.Types.Unique.DFM
import CSlash.Types.Unique.FM
import CSlash.Types.Name.Env

import CSlash.Core.DataCon
import CSlash.Core.TyCon
import CSlash.Core.Kind

import CSlash.Utils.Error
import CSlash.Utils.Outputable
import CSlash.Utils.Logger

import CSlash.Utils.TmpFs

import CSlash.Data.Stream
import CSlash.Data.OrdList

import Control.Monad (when,void, forM_)
import CSlash.Utils.Misc
import System.IO.Unsafe
import qualified Data.ByteString as BS
import Data.IORef
import CSlash.Utils.Panic

codeGen
  :: Logger
  -> TmpFs
  -> StgToPirConfig
  -> [CgStgTopBinding]
  -> CgStream PirGroup ()
codeGen logger tmpfs cfg stg_binds = do
  cgref <- liftIO $ initC >>= \s -> newIORef s
  uniqRnRef <- liftIO $ newIORef emptyDetUFM
  let fstate = initFCodeState $ stgToPirPlatform cfg

  panic "codeGen"
