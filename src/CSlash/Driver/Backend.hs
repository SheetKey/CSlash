module CSlash.Driver.Backend where

import CSlash.Driver.Backend.Internal
import CSlash.Driver.Phases

import CSlash.Utils.Error
import CSlash.Utils.Panic

import CSlash.Driver.Pipeline.Monad
import CSlash.Platform

platformDefaultBackend :: Platform -> Backend
platformDefaultBackend platform
  | platformUnregisterised platform = panic "unregisterised platform"
  | otherwise = llvmBackend

newtype Backend = Named BackendName

instance Show Backend where
  show = backendDescription

llvmBackend :: Backend
llvmBackend = Named LLVM

noBackend :: Backend
noBackend = Named NoBackend

---------------------------------------------------------------------------------

data DefunctionalizedPostCsPipeline
  = LlvmPostCsPipeline
  | NoPostCsPipeline

---------------------------------------------------------------------------------

backendDescription :: Backend -> String
backendDescription (Named LLVM) = "LLVM"
backendDescription (Named NoBackend) = "no code generated"

backendWritesFiles :: Backend -> Bool
backendWritesFiles (Named LLVM) = True
backendWritesFiles (Named NoBackend) = False

backendPipelineOutput :: Backend -> PipelineOutput
backendPipelineOutput (Named LLVM) = Persistent
backendPipelineOutput (Named NoBackend) = NoOutputFile

backendGeneratesCode :: Backend -> Bool
backendGeneratesCode (Named LLVM) = True
backendGeneratesCode (Named NoBackend) = False

backendUnregisterisedAbiOnly :: Backend -> Bool
backendUnregisterisedAbiOnly (Named LLVM) = False
backendUnregisterisedAbiOnly (Named NoBackend) = False

backendSpecialModuleSource :: Backend -> Maybe String
backendSpecialModuleSource (Named LLVM) =  Nothing
backendSpecialModuleSource (Named NoBackend) = Just "nothing"

backendSupportsHpc :: Backend -> Bool
backendSupportsHpc (Named LLVM) = True
backendSupportsHpc (Named NoBackend) = True

backendPostCsPipeline :: Backend -> DefunctionalizedPostCsPipeline
backendPostCsPipeline (Named LLVM) = LlvmPostCsPipeline
backendPostCsPipeline (Named NoBackend) = NoPostCsPipeline

backendNormalSuccessorPhase :: Backend -> Phase
backendNormalSuccessorPhase (Named LLVM) = LlvmOpt
backendNormalSuccessorPhase (Named NoBackend) = StopLn
