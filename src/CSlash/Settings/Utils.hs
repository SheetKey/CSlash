module CSlash.Settings.Utils where

import Data.Char (isSpace)
import Data.Map (Map)
import qualified Data.Map as Map

import CSlash.BaseDir
import CSlash.Platform.ArchOS

maybeRead :: Read a => String -> Maybe a
maybeRead str = case reads str of
  [(x, "")] -> Just x
  _ -> Nothing

maybeReadFuzzy :: Read a => String -> Maybe a
maybeReadFuzzy str = case reads str of
  [(x, s)] | all isSpace s -> Just x
  _ -> Nothing

type RawSettings = Map String String

getTargetArchOS :: FilePath -> RawSettings -> Either String ArchOS
getTargetArchOS settingsFile settings =
  ArchOS <$> readRawSetting settingsFile settings "target arch"
         <*> readRawSetting settingsFile settings "target os"

getRawSetting :: FilePath -> RawSettings -> String -> Either String String
getRawSetting settingsFile settings key = case Map.lookup key settings of
  Just xs -> Right xs
  Nothing -> Left $ "No entry for " ++ show key ++ " in " ++ show settingsFile

getRawFilePathSetting :: FilePath -> FilePath -> RawSettings -> String -> Either String String
getRawFilePathSetting top_dir settingsFile settings key =
  expandTopDir top_dir <$> getRawSetting settingsFile settings key

getRawBooleanSetting :: FilePath -> RawSettings -> String -> Either String Bool
getRawBooleanSetting settingsFile settings key = do
  rawValue <- getRawSetting settingsFile settings key
  case rawValue of
    "YES" -> Right True
    "NO" -> Right False
    xs -> Left $ "Bad value for " ++ show key ++ ": " ++ show xs

readRawSetting :: (Show a, Read a) => FilePath -> RawSettings -> String -> Either String a
readRawSetting settingsFile settings key = case Map.lookup key settings of
  Just xs -> case maybeRead xs of
    Just v -> Right v
    Nothing -> Left $ "Failed to read " ++ show key ++ " value " ++ show xs
  Nothing -> Left $ "No entry for " ++ show key ++ " in " ++ show settingsFile
