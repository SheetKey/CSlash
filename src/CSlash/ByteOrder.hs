module CSlash.ByteOrder where

data ByteOrder
  = BigEndian
  | LittleEndian
  deriving (Eq, Ord, Enum, Show)
