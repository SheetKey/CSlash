{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}

module CSlash.Tc.Zonk.Env where

import CSlash.Core.Type.Rep ( Type )
import CSlash.Core.Kind ( Kind, MonoKind )
import CSlash.Types.Var ( TcTyVar, TyVar, AnyTyVar, TcKiVar, KiVar, AnyKiVar )

import CSlash.Types.Var ( Id )
import CSlash.Types.Var.Env
import CSlash.Types.Id

import CSlash.Utils.Monad.Codensity
import CSlash.Utils.Outputable

import Control.Monad.Fix         ( MonadFix(..) )
import Control.Monad.IO.Class    ( MonadIO(..) )
import Control.Monad.Trans.Class ( MonadTrans(..) )
import Data.Coerce               ( coerce )
import Data.IORef                ( IORef, newIORef )
import Data.List                 ( partition )

import GHC.Exts                  ( oneShot )

data ZonkEnv = ZonkEnv
  { ze_flexi :: !ZonkFlexi
  , ze_tv_env :: MkVarEnv (TyVar KiVar) (TyVar KiVar)
  , ze_kv_env :: MkVarEnv KiVar KiVar
  , ze_id_env :: MkVarEnv ZkId ZkId
  , ze_meta_tv_env :: IORef (MkVarEnv (TcTyVar AnyKiVar) (Type (TyVar KiVar) KiVar))
  , ze_meta_kv_env :: IORef (MkVarEnv TcKiVar (MonoKind KiVar))
  }

data ZonkFlexi
  = NoFlexi

instance Outputable ZonkEnv where
  ppr (ZonkEnv { ze_tv_env = tv_env, ze_kv_env = kv_env, ze_id_env = id_env })
    = text "ZE" <+> braces (vcat [ text "ze_tv_env =" <+> ppr tv_env
                                 , text "ze_kv_env =" <+> ppr kv_env
                                 , text "ze_id_env =" <+> ppr id_env ])

newtype ZonkT m a = ZonkT' { runZonkT :: ZonkEnv -> m a }

{-# COMPLETE ZonkT #-}
pattern ZonkT :: forall m a. (ZonkEnv -> m a) -> ZonkT m a
pattern ZonkT m <- ZonkT' m
  where
    ZonkT m = ZonkT' (oneShot m)

instance Functor m => Functor (ZonkT m) where
  fmap f (ZonkT g) = ZonkT $ \ !env -> fmap f (g env)
  a <$ ZonkT g     = ZonkT $ \ !env -> a <$ g env
  {-# INLINE fmap #-}
  {-# INLINE (<$) #-}

instance Applicative m => Applicative (ZonkT m) where
  pure a = ZonkT (\ !_ -> pure a)
  ZonkT f <*> ZonkT x = ZonkT (\ !env -> f env <*> x env )
  ZonkT m *> f = ZonkT (\ !env -> m env *> runZonkT f env)
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}
  {-# INLINE (*>) #-}

instance Monad m => Monad (ZonkT m) where
  ZonkT m >>= f =
    ZonkT (\ !env -> do r <- m env
                        runZonkT (f r) env )
  (>>)   = (*>)
  {-# INLINE (>>=) #-}
  {-# INLINE (>>) #-}

instance MonadIO m => MonadIO (ZonkT m) where
  liftIO f = ZonkT (\ !_ -> liftIO f)
  {-# INLINE liftIO #-}

instance MonadTrans ZonkT where
  lift ma = ZonkT $ \ !_ -> ma
  {-# INLINE lift #-}

instance MonadFix m => MonadFix (ZonkT m) where
  mfix f = ZonkT $ \ !r -> mfix $ oneShot $ \ a -> runZonkT (f a) r
  {-# INLINE mfix #-}

newtype ZonkBndrT m a = ZonkBndrT { runZonkBndrT' :: forall r. (a -> ZonkT m r) -> ZonkT m r }
  deriving (Functor, Applicative, Monad, MonadIO, MonadFix)
  via Codensity (ZonkT m)

{-# INLINE noBinders #-}
noBinders :: Monad m => ZonkT m a -> ZonkBndrT m a
noBinders z = coerce $ toCodensity z

{-# INLINABLE initZonkEnv #-}
initZonkEnv :: MonadIO m => ZonkFlexi -> ZonkT m b -> m b
initZonkEnv flexi thing_inside = do
  mtv_env_ref <- liftIO $ newIORef emptyVarEnv
  mkv_env_ref <- liftIO $ newIORef emptyVarEnv
  let ze = ZonkEnv { ze_flexi = flexi
                   , ze_tv_env = emptyVarEnv
                   , ze_kv_env = emptyVarEnv
                   , ze_id_env = emptyVarEnv
                   , ze_meta_tv_env = mtv_env_ref 
                   , ze_meta_kv_env = mkv_env_ref }
  runZonkT thing_inside ze

{-# INLINE runZonkBndrT #-}
runZonkBndrT :: ZonkBndrT m a -> forall r. (a -> ZonkT m r) -> ZonkT m r
runZonkBndrT (ZonkBndrT k) f = k (oneShot f)

{-# INLINE nestZonkEnv #-}
nestZonkEnv :: (ZonkEnv -> ZonkEnv) -> ZonkBndrT m ()
nestZonkEnv f = ZonkBndrT $ \k -> case k () of
                                    ZonkT g -> ZonkT (g . f)

{-# INLINE getZonkEnv #-}
getZonkEnv :: Monad m => ZonkT m ZonkEnv
getZonkEnv = ZonkT return

extendIdZonkEnvRec :: [ZkId] -> ZonkBndrT m ()
extendIdZonkEnvRec ids = nestZonkEnv $ \ze@(ZonkEnv { ze_id_env = id_env }) ->
                                         ze { ze_id_env = extendVarEnvList
                                                          id_env [(id, id) | id <- ids] }

extendTyZonkEnv :: TyVar KiVar -> ZonkBndrT m ()
extendTyZonkEnv tv = nestZonkEnv $ \ze@(ZonkEnv { ze_tv_env = ty_env }) ->
                                     ze { ze_tv_env = extendVarEnv ty_env tv tv }

extendKiZonkEnv :: KiVar -> ZonkBndrT m ()
extendKiZonkEnv kv = nestZonkEnv $ \ze@(ZonkEnv { ze_kv_env = ki_env }) ->
                                     ze { ze_kv_env = extendVarEnv ki_env kv kv }
