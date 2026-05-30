module CSlash.Llvm.Config where

import CSlash.Platform

import CSlash.Utils.Outputable
import CSlash.Settings.Utils
import CSlash.Utils.Panic

import System.FilePath

import qualified Data.List.NonEmpty as NE

data LlvmCgConfig = LlvmCgConfig
  { llvmCgPlatform :: !Platform
  , llvmCgContext :: !SDocContext
  , llvmCgFillUndefWithGarbage :: !Bool
  , llvmCgSplitSection :: !Bool
  , llvmAvxEnabled :: !Bool
  , llvmCgBmiVersion :: Maybe BmiVersion
  , llvmCgLlvmVersion :: Maybe LlvmVersion
  , llvmCgDoWarn :: !Bool
  , llvmCgLlvmTarget :: !String
  , llvmCgLlvmConfig :: !LlvmConfig
  }

newtype LlvmVersion = LlvmVersion { llvmVersionNE :: NE.NonEmpty Int }
  deriving (Eq, Ord)

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
