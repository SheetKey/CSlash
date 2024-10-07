{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE KindSignatures #-}

module CSlash.Driver.Pipeline.Monad where

import Control.Monad.IO.Class
import qualified Data.Kind as K
import CSlash.Driver.Phases
import CSlash.Utils.TmpFs

type TPipelineClass (f :: K.Type -> K.Type) (m :: K.Type -> K.Type)
  = (Functor m, MonadIO m, Applicative m, Monad m, MonadUse f m)

class MonadUse f m where
  use :: f a -> m a

data PipeEnv = PipeEnv
  { stop_phase :: StopPhase
  , src_filename :: String
  , src_basename :: String
  , src_suffix :: String
  , start_phase :: Phase
  , output_spec :: PipelineOutput
  }

data PipelineOutput
  = Temporary TempFileLifetime
  | Persistent
  | SpecificFile
  | NoOutputFile
  deriving Show
