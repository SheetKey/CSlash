{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}

module CSlash.Tc.Zonk.Env where

import CSlash.Cs.Pass

import CSlash.Core.Type.Rep ( Type )
import CSlash.Core.Kind ( Kind, MonoKind, KindCoercion )
import CSlash.Types.Var
  ( TcTyVar, TyVar, TcKiVar, KiVar, KiCoVar, TcKiCoVar )

import CSlash.Types.Var ( Id )
import CSlash.Types.Var.Env
import CSlash.Types.Var.Id

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
  , ze_tv_env :: VarEnv (TyVar Zk) (TyVar Zk)
  , ze_kcv_env :: VarEnv (KiCoVar Zk) (KiCoVar Zk)
  , ze_kv_env :: VarEnv (KiVar Zk) (KiVar Zk)
  , ze_id_env :: VarEnv (Id Zk) (Id Zk)
  , ze_meta_tv_env :: IORef (VarEnv TcTyVar (Type Zk))
  , ze_meta_kcv_env :: IORef (VarEnv TcKiCoVar (KindCoercion Zk))
  , ze_meta_kv_env :: IORef (VarEnv TcKiVar (MonoKind Zk))
  }

data ZonkFlexi
  = NoFlexi
  | DefaultFlexiKi

instance Outputable ZonkEnv where
  ppr (ZonkEnv { ze_tv_env = tv_env, ze_kcv_env = kcv_env, ze_kv_env = kv_env, ze_id_env = id_env })
    = text "ZE" <+> braces (vcat [ text "ze_tv_env =" <+> ppr tv_env
                                 , text "ze_kcv_env =" <+> ppr kcv_env
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

don'tBind :: Monad m => ZonkBndrT m a -> ZonkT m a
don'tBind (ZonkBndrT k) = fromCodensity (Codensity k)
{-# INLINE don'tBind #-}

{-# INLINABLE initZonkEnv #-}
initZonkEnv :: MonadIO m => ZonkFlexi -> ZonkT m b -> m b
initZonkEnv flexi thing_inside = do
  mtv_env_ref <- liftIO $ newIORef emptyVarEnv
  mkcv_env_ref <- liftIO $ newIORef emptyVarEnv
  mkv_env_ref <- liftIO $ newIORef emptyVarEnv
  let ze = ZonkEnv { ze_flexi = flexi
                   , ze_tv_env = emptyVarEnv
                   , ze_kcv_env = emptyVarEnv
                   , ze_kv_env = emptyVarEnv
                   , ze_id_env = emptyVarEnv
                   , ze_meta_tv_env = mtv_env_ref 
                   , ze_meta_kcv_env = mkcv_env_ref 
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

extendIdZonkEnvRec :: [Id Zk] -> ZonkBndrT m ()
extendIdZonkEnvRec ids = nestZonkEnv $ \ze@(ZonkEnv { ze_id_env = id_env }) ->
                                         ze { ze_id_env = extendVarEnvList
                                                          id_env [(id, id) | id <- ids] }

extendIdZonkEnv :: Id Zk -> ZonkBndrT m ()
extendIdZonkEnv id = nestZonkEnv $ \ze@(ZonkEnv { ze_id_env = id_env }) ->
                                     ze { ze_id_env = extendVarEnv id_env id id }

extendTyZonkEnv :: TyVar Zk -> ZonkBndrT m ()
extendTyZonkEnv tv = nestZonkEnv $ \ze@(ZonkEnv { ze_tv_env = ty_env }) ->
                                     ze { ze_tv_env = extendVarEnv ty_env tv tv }

extendKiCoZonkEnv :: KiCoVar Zk -> ZonkBndrT m ()
extendKiCoZonkEnv kcv = nestZonkEnv $ \ze@(ZonkEnv { ze_kcv_env = kcv_env }) ->
                                        ze { ze_kcv_env = extendVarEnv kcv_env kcv kcv }

extendKiZonkEnv :: KiVar Zk -> ZonkBndrT m ()
extendKiZonkEnv kv = nestZonkEnv $ \ze@(ZonkEnv { ze_kv_env = ki_env }) ->
                                     ze { ze_kv_env = extendVarEnv ki_env kv kv }
