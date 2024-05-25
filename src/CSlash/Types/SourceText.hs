module CSlash.Types.SourceText where

import GHC.Data.FastString

data SourceText
  = SourceText FastString
  | NoSourceText
  deriving (Data, Show, Eq)
