module CSlash.Utils.CliOption where

data Option
  = FileOption String String
  | Option String
  deriving (Eq)

showOpt :: Option -> String
showOpt (FileOption pre f) = pre ++ f
showOpt (Option s) = s
