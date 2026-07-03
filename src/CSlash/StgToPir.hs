module CSlash.StgToPir (codeGen) where

import CSlash.Pir.UniqueRenamer
-- import CSlash.StgToPir.Prof (initCostCentres, ldvEnter)
import CSlash.StgToPir.Monad
import CSlash.StgToPir.Env
import CSlash.StgToPir.Bind
-- import CSlash.StgToPir.DataCon
-- import CSlash.StgToPir.Layout
-- import CSlash.StgToPir.Utils
import CSlash.StgToPir.Function
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
  let cg :: FCode a -> CgStream PirGroup a
      cg fcode = do
        (a, pir) <- liftIO . withTimingSilent logger (text "STG -> Pir") (`seq` ()) $ do
          st <- readIORef cgref
          rnm0 <- readIORef uniqRnRef

          let ((a, pir), st') = runC cfg fstate st (getPir fcode)
              (rnm1, pir_renamed) =
                if stgToPirObjectDeterminism cfg
                then panic "object determinism"
                else (rnm0, removeDeterm pir)

          writeIORef cgref $! (st' { cgs_tops = nilOL, cgs_stmts = mkNop })
          writeIORef uniqRnRef $! rnm1

          return (a, pir_renamed)
          
        yield pir
        return a

  mapM_ (cg . cgTopBinding logger tmpfs cfg) stg_binds

  panic "codeGen"

---------------------------------------------------------------
--      Top-level bindings
---------------------------------------------------------------

cgTopBinding :: Logger -> TmpFs -> StgToPirConfig -> CgStgTopBinding -> FCode ()
cgTopBinding logger tmpfs cfg stg_bind = case stg_bind of
  StgTopBind (StgNonRec id rhs) -> do
    let (info, fcode) = cgTopRhs cfg NonRecursive id rhs
    fcode
    addBindC info

  _ -> panic "cgTopBinding unfinished"

cgTopRhs :: StgToPirConfig -> RecFlag -> CgId -> CgStgRhs -> (CgIdInfo, FCode ())
cgTopRhs cfg _ bndr (StgRhsCon {}) = panic "cgTopRhs Con"

cgTopRhs cfg is_rec bndr (StgRhsClosure fvs is_join args body _)
  = assertPpr (isEmptyDVarSet fvs) (text "fvs:" <+> ppr fvs) $
    assertPpr (not is_join) (text "cgTopRhs is_join") $
    cgTopRhsFunction (stgToPirPlatform cfg) is_rec bndr args body
