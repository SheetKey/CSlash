module CSlash.PirToLlvm.Version.Bounds where

import CSlash.PirToLlvm.Version.Type

import qualified Data.List.NonEmpty as NE

-- | The (inclusive) lower bound on the LLVM Version that is currently supported.
supportedLlvmVersionLowerBound :: LlvmVersion
supportedLlvmVersionLowerBound = LlvmVersion (18 NE.:| [])

-- | The (not-inclusive) upper bound  bound on the LLVM Version that is currently supported.
supportedLlvmVersionUpperBound :: LlvmVersion
supportedLlvmVersionUpperBound = LlvmVersion (18 NE.:| [])
