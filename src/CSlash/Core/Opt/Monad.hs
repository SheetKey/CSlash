{-# LANGUAGE DeriveFunctor #-}

module CSlash.Core.Opt.Monad where

import Prelude hiding (read)

import CSlash.Driver.DynFlags
import CSlash.Driver.Env

import CSlash.Core.Rules     ( RuleBase, RuleEnv, mkRuleEnv )
import CSlash.Core.Opt.Stats ( SimplCount, zeroSimplCount, plusSimplCount )

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
  , cr_rule_base :: RuleBase
  , cr_module :: Module
  , cr_name_ppr_ctx :: NamePprCtx
  , cr_loc :: SrcSpan
  , cr_uniq_tag :: !Char
  }

newtype CoreWriter = CoreWriter
  { cw_simpl_count :: SimplCount }

type CoreIOEnv = IOEnv CoreReader

newtype CoreM a = CoreM { unCoreM :: CoreIOEnv (a, CoreWriter) }
  deriving Functor

emptyWriter :: Bool -> CoreWriter
emptyWriter dump_simpl_stats = CoreWriter
  { cw_simpl_count = zeroSimplCount dump_simpl_stats }

plusWriter :: CoreWriter -> CoreWriter -> CoreWriter
plusWriter w1 w2 = CoreWriter
  { cw_simpl_count = (cw_simpl_count w1) `plusSimplCount` (cw_simpl_count w2) }

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

runCoreM
  :: CsEnv
  -> RuleBase
  -> Char
  -> Module
  -> NamePprCtx
  -> SrcSpan
  -> CoreM a
  -> IO (a, SimplCount)
runCoreM cs_env rule_base tag mod name_ppr_ctx loc m
  = liftM extract $ runIOEnv reader $ unCoreM m
  where
    reader = CoreReader { cr_cs_env = cs_env
                        , cr_rule_base = rule_base
                        , cr_module = mod
                        , cr_name_ppr_ctx = name_ppr_ctx
                        , cr_loc = loc
                        , cr_uniq_tag = tag }

    extract :: (a, CoreWriter) -> (a, SimplCount)
    extract (value, writer) = (value, cw_simpl_count writer)

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

liftIOWithCount :: IO (SimplCount, a) -> CoreM a
liftIOWithCount what = liftIO what >>= (\(count, x) -> addSimplCount count >> return x)

{- *********************************************************************
*                                                                      *
            Reader, writer, and state
*                                                                      *
********************************************************************* -}
 
getCsEnv :: CoreM CsEnv
getCsEnv = read cr_cs_env

getHomeRuleBase :: CoreM RuleBase
getHomeRuleBase = read cr_rule_base

initRuleEnv :: ModGuts -> CoreM RuleEnv
initRuleEnv guts = do
  hpt_rules <- getHomeRuleBase
  eps_rules <- getExternalRuleBase
  return $ mkRuleEnv guts eps_rules hpt_rules

getExternalRuleBase :: CoreM RuleBase
getExternalRuleBase = eps_rule_base <$> get_eps

getNamePprCtx :: CoreM NamePprCtx
getNamePprCtx = read cr_name_ppr_ctx

addSimplCount :: SimplCount -> CoreM ()
addSimplCount count = write (CoreWriter { cw_simpl_count = count })

instance HasDynFlags CoreM where
  getDynFlags = fmap cs_dflags getCsEnv

instance HasLogger CoreM where
  getLogger = fmap cs_logger getCsEnv

instance HasModule CoreM where
  getModule = read cr_module

get_eps :: CoreM ExternalPackageState
get_eps = do
  cs_env <- getCsEnv
  liftIO $ csEPS cs_env
