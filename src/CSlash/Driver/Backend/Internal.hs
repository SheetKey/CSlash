module CSlash.Driver.Backend.Internal where

data BackendName
  = LLVM
  | NoBackend
  deriving (Eq, Show)
