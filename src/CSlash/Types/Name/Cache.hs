module CSlash.Types.Name.Cache where

import CSlash.Unit.Module
import CSlash.Types.Name
import CSlash.Types.Unique.Supply
import CSlash.Builtin.Types
import CSlash.Builtin.Names

import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Control.Concurrent.MVar
import Control.Monad
import Control.Applicative

data NameCache = NameCache
  { nsUniqChar :: {-# UNPACK #-} !Char
  , nsNames :: {-# UNPACK #-} !(MVar OrigNameCache)
  }

type OrigNameCache = ModuleEnv (OccEnv Name)

extendOrigNameCache' :: OrigNameCache -> Name -> OrigNameCache
extendOrigNameCache' nc name
  = assertPpr (isExternalName name) (ppr name) $
    extendOrigNameCache nc (nameModule name) (nameOccName name) name

extendOrigNameCache :: OrigNameCache -> Module -> OccName -> Name -> OrigNameCache
extendOrigNameCache nc mod occ name
  = extendModuleEnvWith combine nc mod (unitOccEnv occ name)
  where
    combine _ occ_env = extendOccEnv occ_env occ name

initNameCache :: Char -> [Name] -> IO NameCache
initNameCache c names = NameCache c <$> newMVar (initOrigNames names)

initOrigNames :: [Name] -> OrigNameCache
initOrigNames names = foldl' extendOrigNameCache' emptyModuleEnv names
