{-# LANGUAGE DeriveFunctor #-}

module CSlash.Core.Opt.Monad where

import Prelude hiding (read)

import CSlash.Driver.DynFlags
import CSlash.Driver.Env

-- import GHC.Core.Rules     ( RuleBase, RuleEnv, mkRuleEnv )
-- import GHC.Core.Opt.Stats ( SimplCount, zeroSimplCount, plusSimplCount )

-- import GHC.Types.Annotations
import CSlash.Types.Unique.Supply
import CSlash.Types.Name.Env
import CSlash.Types.SrcLoc
import CSlash.Types.Error

import CSlash.Utils.Error ( errorDiagnostic )
import CSlash.Utils.Outputable as Outputable
import CSlash.Utils.Logger
import CSlash.Utils.Monad
import CSlash.Utils.Panic

import CSlash.Data.IOEnv hiding     ( liftIO, failM, failWithM )
import qualified CSlash.Data.IOEnv  as IOEnv

import CSlash.Unit.Module
import CSlash.Unit.Module.ModGuts
import CSlash.Unit.External

import Data.Bifunctor ( bimap )
import Data.Dynamic
import Data.Maybe (listToMaybe)
import Data.Word
import Control.Monad
import Control.Applicative ( Alternative(..) )

data FloatOutSwitches = FloatOutSwitches
  { floatOutAllLambdas :: Bool
  , floatOutConstants :: Bool
  , floatOutOverSatApps :: Bool
  , floatToTopLevelOnly :: Bool
  , floatJoinsToTop :: Bool
  }

instance Outputable FloatOutSwitches where
  ppr = pprFloatOutSwitches

pprFloatOutSwitches :: FloatOutSwitches -> SDoc
pprFloatOutSwitches sw
  = text "FOD" <+> (braces $
                    sep $ punctuate comma $
                    [ text "Lam =" <+> ppr (floatOutAllLambdas sw)
                    , text "Consts =" <+> ppr (floatOutConstants sw)
                    , text "JoinsToTop =" <+> ppr (floatJoinsToTop sw)
                    , text "OverSatApps =" <+> ppr (floatOutOverSatApps sw) ])

{- *********************************************************************
*                                                                      *
            Monad and carried data structures
*                                                                      *
********************************************************************* -}

data CoreReader = CoreReader
  { cr_cs_env :: CsEnv
  , cr_module :: Module
  , cr_name_ppr_ctx :: NamePprCtx
  , cr_loc :: SrcSpan
  , cr_uniq_tag :: !Char
  }

newtype CoreWriter = CoreWriter
  { cw_simpl_count :: () {-SimplCount-} }

type CoreIOEnv = IOEnv CoreReader

newtype CoreM a = CoreM { unCoreM :: CoreIOEnv (a, CoreWriter) }
  deriving Functor

emptyWriter :: Bool -> CoreWriter
emptyWriter dump_simpl_stats = panic "emptyWriter"

plusWriter :: CoreWriter -> CoreWriter -> CoreWriter
plusWriter w1 w2 = panic "plusWriter"

instance Applicative CoreM where
  pure x = CoreM $ nop x
  (<*>) = ap
  m *> k = m >>= \_ -> k

instance Monad CoreM where
  mx >>= f = CoreM $ do
    (x, w1) <- unCoreM mx
    (y, w2) <- unCoreM (f x)
    let w = w1 `plusWriter` w2
    return $ seq w (y, w)

instance Alternative CoreM where
  empty = CoreM Control.Applicative.empty
  m <|> n = CoreM (unCoreM m <|> unCoreM n)

instance MonadPlus CoreM

instance MonadUnique CoreM where
  getUniqueSupplyM = do
    tag <- read cr_uniq_tag
    liftIO $! mkSplitUniqSupply tag

  getUniqueM = do
    tag <- read cr_uniq_tag
    liftIO $! uniqFromTag tag

{- *********************************************************************
*                                                                      *
            Core combinators
*                                                                      *
********************************************************************* -}

nop :: a -> CoreIOEnv (a, CoreWriter)
nop x = do
  logger <- cs_logger . cr_cs_env <$> getEnv
  return (x, emptyWriter $ logHasDumpFlag logger Opt_D_dump_simpl_stats)

read :: (CoreReader -> a) -> CoreM a
read f = CoreM $ getEnv >>= (\r -> nop (f r))

write :: CoreWriter -> CoreM ()
write w = CoreM $ return ((), w)

liftIOEnv :: CoreIOEnv a -> CoreM a
liftIOEnv mx = CoreM (mx >>= (\x -> nop x))

instance MonadIO CoreM where
  liftIO = liftIOEnv . IOEnv.liftIO

-- liftIOWithCount :: IO (SimplCount, a) -> CoreM a
-- liftIOWithCount what = liftIO what >>= (\(count, x) -> addSimplCount 

{- *********************************************************************
*                                                                      *
            Reader, writer, and state
*                                                                      *
********************************************************************* -}

