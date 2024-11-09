{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE PatternSynonyms #-}

module CSlash.Tc.Zonk.Monad where

import CSlash.Driver.Flags ( DumpFlag(Opt_D_dump_tc_trace) )

import CSlash.Types.SrcLoc ( SrcSpan )

import CSlash.Tc.Types.BasicTypes ( TcBinderStack )
import CSlash.Tc.Utils.TcType   ( TcLevel )

import CSlash.Utils.Logger
import CSlash.Utils.Outputable

import Control.Monad          ( when )
import Control.Monad.IO.Class ( MonadIO(..) )

import GHC.Exts               ( oneShot )

data ZonkGblEnv = ZonkGblEnv
  { zge_logger :: Logger
  , zge_name_ppr_ctx :: NamePprCtx
  , zge_src_span :: SrcSpan
  , zge_tc_level :: TcLevel
  , zge_binder_stack :: TcBinderStack
  }

newtype ZonkM a = ZonkM' { runZonkM :: ZonkGblEnv -> IO a }

pattern ZonkM :: forall a. (ZonkGblEnv -> IO a) -> ZonkM a
pattern ZonkM m <- ZonkM' m
  where
    ZonkM m = ZonkM' (oneShot m)
{-# COMPLETE ZonkM #-}

instance Functor ZonkM where
  fmap f (ZonkM g) = ZonkM $ \ !env -> fmap f (g env)
  a <$ ZonkM g = ZonkM $ \ !env -> a <$ g env
  {-# INLINE fmap #-}
  {-# INLINE (<$) #-}

instance Applicative ZonkM where
  pure a = ZonkM (\ !_ -> pure a)
  ZonkM f <*> ZonkM x = ZonkM (\ !env -> f env <*> x env)
  ZonkM m *> f = ZonkM (\ !env -> m env *> runZonkM f env)
  {-# INLINE pure #-}
  {-# INLINE (<*>) #-}
  {-# INLINE (*>) #-}

instance Monad ZonkM where
  ZonkM m >>= f =
    ZonkM (\ !env -> do r <- m env
                        runZonkM (f r) env)
  (>>) = (*>)
  {-# INLINE (>>=) #-}
  {-# INLINE (>>) #-}

instance MonadIO ZonkM where
  liftIO f = ZonkM (\ !_ -> f)
  {-# INLINE liftIO #-}

getZonkGblEnv :: ZonkM ZonkGblEnv
getZonkGblEnv = ZonkM return
