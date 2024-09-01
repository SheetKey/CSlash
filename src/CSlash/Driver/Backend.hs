module CSlash.Driver.Backend where

import CSlash.Driver.Backend.Internal

import CSlash.Utils.Error
import CSlash.Utils.Panic

newtype Backend = Named BackendName
