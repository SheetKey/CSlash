module CSlash.Driver.LlvmConfigCache where

import CSlash.Llvm.Config

import System.IO.Unsafe

data LlvmConfigCache = LlvmConfigCache LlvmConfig

initLlvmConfigCache :: FilePath -> IO LlvmConfigCache
initLlvmConfigCache top_dir = pure $ LlvmConfigCache (unsafePerformIO $ initLlvmConfig top_dir)
