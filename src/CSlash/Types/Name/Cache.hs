{-# LANGUAGE BangPatterns #-}

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

takeUniqFromNameCache :: NameCache -> IO Unique
takeUniqFromNameCache (NameCache c _) = uniqFromTag c

lookupOrigNameCache :: OrigNameCache -> Module -> OccName -> Maybe Name
lookupOrigNameCache nc mod occ
  | mod == cSLASH_TYPES || mod == cSLASH_PRIM || mod == cSLASH_BUILTIN
  , Just name <- isBuiltInOcc_maybe occ <|> isPunOcc_maybe mod occ
  = Just name
  | otherwise
  = case lookupModuleEnv nc mod of
      Nothing -> Nothing
      Just occ_env -> lookupOccEnv occ_env occ

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

updateNameCache'
  :: NameCache
  -> (OrigNameCache -> IO (OrigNameCache, c))
  -> IO c
updateNameCache' (NameCache _ nc) upd_fn = modifyMVar' nc upd_fn

modifyMVar' :: MVar a -> (a -> IO (a, b)) -> IO b
modifyMVar' m f = modifyMVar m $ f >=> \c -> fst c `seq` pure c

updateNameCache
  :: NameCache -> Module -> OccName -> (OrigNameCache -> IO (OrigNameCache, c)) -> IO c
updateNameCache name_cache !_mod !_occ upd_fn = updateNameCache' name_cache upd_fn
