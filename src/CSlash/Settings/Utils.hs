module CSlash.Settings.Utils where

import Data.Char (isSpace)

maybeReadFuzzy :: Read a => String -> Maybe a
maybeReadFuzzy str = case reads str of
  [(x, s)] | all isSpace s -> Just x
  _ -> Nothing
