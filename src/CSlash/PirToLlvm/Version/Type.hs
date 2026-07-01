module CSlash.PirToLlvm.Version.Type where

import qualified Data.List.NonEmpty as NE

newtype LlvmVersion = LlvmVersion { llvmVersionNE :: NE.NonEmpty Int }
  deriving (Eq, Ord)
