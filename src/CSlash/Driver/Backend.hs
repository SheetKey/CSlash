module CSlash.Driver.Backend where

import CSlash.Driver.Backend.Internal
import CSlash.Driver.Phases

import CSlash.Utils.Error
import CSlash.Utils.Panic

import CSlash.Platform

platformDefaultBackend :: Platform -> Backend
platformDefaultBackend platform
  | platformUnregisterised platform = panic "unregisterised platform"
  | otherwise = llvmBackend

newtype Backend = Named BackendName

llvmBackend :: Backend
llvmBackend = Named LLVM

noBackend :: Backend
noBackend = Named NoBackend

---------------------------------------------------------------------------------

backendDescription :: Backend -> String
backendDescription (Named LLVM) = "LLVM"
backendDescription (Named NoBackend) = "no code generated"

backendWritesFiles :: Backend -> Bool
backendWritesFiles (Named LLVM) = True
backendWritesFiles (Named NoBackend) = False

backendGeneratesCode :: Backend -> Bool
backendGeneratesCode (Named LLVM) = True
backendGeneratesCode (Named NoBackend) = False

backendUnregisterisedAbiOnly :: Backend -> Bool
backendUnregisterisedAbiOnly (Named LLVM) = False
backendUnregisterisedAbiOnly (Named NoBackend) = False

backendSupportsHpc :: Backend -> Bool
backendSupportsHpc (Named LLVM) = True
backendSupportsHpc (Named NoBackend) = True

backendNormalSuccessorPhase :: Backend -> Phase
backendNormalSuccessorPhase (Named LLVM) = LlvmOpt
backendNormalSuccessorPhase (Named NoBackend) = StopLn
