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

backendWritesFiles :: Backend -> Bool
backendWritesFiles (Named LLVM) = True
backendWritesFiles (Named NoBackend) = False
