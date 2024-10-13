module CSlash.Driver.Phases where

import CSlash.Platform

-- import GHC.ForeignSrcLang

import CSlash.Types.SourceFile

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc

import System.FilePath

data StopPhase
  = StopPreprocess
  | StopAs
  | NoStop

stopPhaseToPhase :: StopPhase -> Phase
stopPhaseToPhase StopPreprocess = anyCs
stopPhaseToPhase StopAs = As
stopPhaseToPhase NoStop = StopLn

data Phase
  = Cs CsSource
  | As
  | LlvmOpt
  | LlvmLlc
  | MergeForeign
  | StopLn
  deriving (Eq, Show)

instance Outputable Phase where
  ppr p = text (show p)

anyCs :: Phase
anyCs = Cs (panic "anyCs")

eqPhase :: Phase -> Phase -> Bool
eqPhase (Cs _) (Cs _) = True
eqPhase As As = True
eqPhase LlvmOpt LlvmOpt = True
eqPhase LlvmLlc LlvmLlc = True
eqPhase MergeForeign MergeForeign = True
eqPhase StopLn StopLn = True
eqPhase _ _ = False

startPhase :: String -> Phase
startPhase "csl" = Cs CsSrcFile
startPhase "s" = As
startPhase "ll" = LlvmOpt
startPhase "bs" = LlvmLlc
startPhase "o" = StopLn
startPhase _ = StopLn

phaseInputExt :: Phase -> String
phaseInputExt (Cs _) = panic "phaseInputExt (Cs _)"
phaseInputExt As = "s"
phaseInputExt LlvmOpt = "ll"
phaseInputExt LlvmLlc = "bc"
phaseInputExt MergeForeign = "o"
phaseInputExt StopLn = "o"

csish_src_suffixes :: [String]
csish_src_suffixes = csish_user_src_suffixes

csish_suffixes :: [String]
csish_suffixes = csish_src_suffixes

csish_user_src_suffixes :: [String]
csish_user_src_suffixes = [ "csl" ]

isCsishSuffix :: String -> Bool
isCsishSuffix s = s `elem` csish_suffixes

isCsSrcSuffix :: String -> Bool
isCsSrcSuffix s = s `elem` csish_src_suffixes

isCsUserSrcSuffix :: String -> Bool
isCsUserSrcSuffix s = s `elem` csish_user_src_suffixes

isSourceSuffix :: String -> Bool
isSourceSuffix suff
  = isCsishSuffix suff

isCsSrcFilename :: FilePath -> Bool
isCsSrcFilename f = isCsSrcSuffix (drop 1 $ takeExtension f)

isCsUserSrcFilename :: FilePath -> Bool
isCsUserSrcFilename f = isCsUserSrcSuffix (drop 1 $ takeExtension f)

isSourceFilename :: FilePath -> Bool
isSourceFilename f = isSourceSuffix (drop 1 $ takeExtension f)

isCsishTarget :: (String, Maybe Phase) -> Bool
isCsishTarget (f, Nothing) = looksLikeModuleName f || isCsSrcFilename f || not (hasExtension f)
isCsishTarget (_, Just phase) =
  phase `notElem` [ As, StopLn ]
