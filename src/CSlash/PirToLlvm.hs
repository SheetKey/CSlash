module CSlash.PirToLlvm where

-- import CSlash.Llvm
-- import GHC.CmmToLlvm.Base
-- import GHC.CmmToLlvm.CodeGen
import CSlash.PirToLlvm.Config
-- import GHC.CmmToLlvm.Data
-- import GHC.CmmToLlvm.Ppr
-- import GHC.CmmToLlvm.Regs
-- import GHC.CmmToLlvm.Mangler
-- import GHC.CmmToLlvm.Version

import CSlash.StgToPir.CgUtils ( {-fixStgRegisters,-} CgStream )
import CSlash.Pir
import CSlash.Pir.Dataflow.Label

import CSlash.Types.Unique.DSM
import CSlash.Utils.BufHandle
import CSlash.Driver.DynFlags
import CSlash.Platform ( platformArch, Arch(..) )
import CSlash.Utils.Error
import CSlash.Data.FastString
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Logger
import qualified CSlash.Data.Stream as Stream

import Control.Monad ( when, forM_ )
import Data.Maybe ( fromMaybe, catMaybes, isNothing )
import System.IO

-- -----------------------------------------------------------------------------
-- Top-level of the LLVM Code generator

llvmCodeGen
  :: Logger
  -> LlvmCgConfig
  -> Handle
  -> DUniqSupply
  -> CgStream RawPirGroup a
  -> IO a
llvmCodeGen logger cfg h dus pir_stream = withTiming logger (text "LLVM CodeGen") (const ()) $ do
  panic "llvmCodeGen"
  -- bufh <- newBufHandle h

  -- showPass logger "LLVM CodeGen"

  -- let mb_ver = llvmCgLlvmVersion cfg

  -- forM_ mb_ver $ \ver -> do
  --   debugTraceMsg logger 2 (text "Using LLVM version:" <+> text (llvmVersionStr ver))
  --   let doWarn = llvmCgDoWarn cfg
  --   when (not (llvmVersionSupported ver) && doWarn) $ putMsg logger $
  --     "You are using an unsupported version of LLVM!" $$
  --     "Currently only" <+> text (llvmVersionStr supportedLlvmVersionLowerBound) <+>
  --     "up to" <+> text (llvmVersionStr supoprtedLlvmVersionUpperBound) <+>
  --     "(non inclusive) is supported." <+>
  --     "System LLVM version: " <> text (llvmVersionStr ver) $$
  --     "We will try though..."

  --   when (isNothing mb_ver) $ do
  --     let doWarn = llvmCgDoWarn cfg
  --     when doWarn $ putMsg logger $
  --       "Failed to detect LLVM version!" $$
  --       "Make sure LLVM is installed correctly." $$
  --       "We will try though..."

  -- let llvm_ver = fromMaybe supportedLlvmVersionLowerBound mb_ver

  -- (a, _) <- runLlvm logger cfg llvm_ver bufh dus $ llvmCodeGen' cfg pir_stream

  -- bFlush bufh

  -- return a

-- llvmCodeGen'
--   :: LlvmCgConfig
--   -> CgStream RawPirGroup a
--   -> LlvmM a
-- llvmCodeGen'
