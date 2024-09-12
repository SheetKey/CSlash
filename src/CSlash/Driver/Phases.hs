module CSlash.Driver.Phases where

import CSlash.Platform

-- import GHC.ForeignSrcLang

import CSlash.Types.SourceFile

import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc

import System.FilePath

data StopPhase
  = NoStop

data Phase
  = Cs CsSource
  | StopLn
  deriving (Eq, Show)

instance Outputable Phase where
  ppr p = text (show p)

startPhase :: String -> Phase
startPhase "csl" = Cs CsSrcFile

csish_src_suffixes :: [String]
csish_src_suffixes = [ "csl" ]

csish_suffixes :: [String]
csish_suffixes = csish_src_suffixes

isCsishSuffix :: String -> Bool
isCsishSuffix s = s `elem` csish_suffixes

isCsSrcSuffix :: String -> Bool
isCsSrcSuffix s = s `elem` csish_src_suffixes

isSourceSuffix :: String -> Bool
isSourceSuffix suff
  = isCsishSuffix suff

isCsSrcFilename :: FilePath -> Bool
isCsSrcFilename f = isCsSrcSuffix (drop 1 $ takeExtension f)

isSourceFilename :: FilePath -> Bool
isSourceFilename f = isSourceSuffix (drop 1 $ takeExtension f)
