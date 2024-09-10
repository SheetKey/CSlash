module CSlash.Llvm.Config where

import CSlash.Platform

import CSlash.Utils.Outputable
import CSlash.Settings.Utils
import CSlash.Utils.Panic
-- import GHC.CmmToLlvm.Version.Type (LlvmVersion)

import System.FilePath

data LlvmTarget = LlvmTarget
  { lDataLayout :: String
  , lCPU :: String
  , lAttributes :: [String]
  }

initLlvmConfig :: FilePath -> IO LlvmConfig
initLlvmConfig top_dir
  = do
    targets <- readAndParse "llvm-targets"
    passes <- readAndParse "llmv-passes"
    return $ LlvmConfig
      { llvmTargets = fmap mkLlvmTarget <$> targets
      , llvmPasses = passes
      }
  where
    readAndParse :: Read a => String -> IO a
    readAndParse name = do
      let f = top_dir </> name
      llvmConfigStr <- readFile f
      case maybeReadFuzzy llvmConfigStr of
        Just s -> return s
        Nothing -> pgmError ("Can't parse LLVM config file: " ++ show f)
    mkLlvmTarget :: (String, String, String) -> LlvmTarget
    mkLlvmTarget (dl, cpu, attrs) = LlvmTarget dl cpu (words attrs)

data LlvmConfig = LlvmConfig
  { llvmTargets :: [(String, LlvmTarget)]
  , llvmPasses :: [(Int, String)]
  }
