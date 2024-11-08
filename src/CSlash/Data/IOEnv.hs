module CSlash.Data.IOEnv ( module X ) where

import GHC.Data.IOEnv as X

import CSlash.Driver.DynFlags
import CSlash.Utils.Logger
import CSlash.Unit.Module

instance ContainsDynFlags env => HasDynFlags (IOEnv env) where
    getDynFlags = do env <- getEnv
                     return $! extractDynFlags env

instance ContainsLogger env => HasLogger (IOEnv env) where
    getLogger = do env <- getEnv
                   return $! extractLogger env

instance ContainsModule env => HasModule (IOEnv env) where
    getModule = do env <- getEnv
                   return $ extractModule env
