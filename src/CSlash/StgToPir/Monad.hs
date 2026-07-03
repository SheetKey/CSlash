{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

module CSlash.StgToPir.Monad
  ( module CSlash.StgToPir.Monad
  , module CSlash.StgToPir.Sequel
  ) where

import CSlash.Cs.Pass
import CSlash.Platform
import CSlash.Platform.Profile
import CSlash.Pir
import CSlash.StgToPir.Config
import CSlash.StgToPir.Function
import CSlash.StgToPir.Sequel
import CSlash.Pir.Graph
import CSlash.Pir.BlockId
import CSlash.Pir.PLabel
-- import GHC.Runtime.Heap.Layout
import CSlash.Unit
import CSlash.Types.Var.Id
import CSlash.Types.Var.Env
import CSlash.Data.OrdList
import CSlash.Types.Basic( ConTagZ )
import CSlash.Types.Unique
import CSlash.Types.Unique.Supply as US
import qualified CSlash.Types.Unique.DSM as DSM ( MonadGetUnique, getUniqueM )
import CSlash.Data.FastString
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Constants (debugIsOn)
import GHC.Exts (oneShot)

import Control.Monad
import Data.List (mapAccumL)

--------------------------------------------------------
-- The FCode monad and its types

newtype FCode a = FCode' { doFCode :: StgToPirConfig -> FCodeState -> CgState -> (a, CgState) }

instance Functor FCode where
  fmap f (FCode m) =
    FCode $ \cfg fst state ->
              case m cfg fst state of
                (x, state') -> (f x, state')

{-# COMPLETE FCode #-}
pattern FCode :: (StgToPirConfig -> FCodeState -> CgState -> (a, CgState)) -> FCode a
pattern FCode m <- FCode' m
  where
    FCode m = FCode' $ oneShot (\cfg -> oneShot
                                 (\fstate -> oneShot
                                   (\state -> m cfg fstate state)))

instance Applicative FCode where
  pure val = FCode $ \_ _ state -> (val, state)
  {-# INLINE pure #-}
  (<*>) = ap

instance Monad FCode where
  FCode m >>= k = FCode $
    \cfg fstate state -> case m cfg fstate state of
                           (m_result, new_state) -> case k m_result of
                                                      FCode kcode -> kcode cfg fstate new_state
  {-# INLINE (>>=) #-}

instance MonadUnique FCode where
  getUniqueSupplyM = cgs_uniqs <$> getState
  getUniqueM = FCode $ \_ _ st ->
    let (u, us') = takeUniqFromSupply (cgs_uniqs st)
    in (u, st { cgs_uniqs = us' })

instance DSM.MonadGetUnique FCode where
  getUniqueM = US.getUniqueM

initC :: IO CgState
initC = do
  uniqs <- mkSplitUniqSupply 'c'
  return (initCgState uniqs)

runC :: StgToPirConfig -> FCodeState -> CgState -> FCode a -> (a, CgState)
runC cfg fst st fcode = doFCode fcode cfg fst st

fixC :: (a -> FCode a) -> FCode a
fixC fcode = FCode $
  \cfg fstate state ->
    let (v, s) = doFCode (fcode v) cfg fstate state
    in (v, s)

--------------------------------------------------------
--        The code generator environment

type CgBindings = IdEnv Zk CgIdInfo
type CgId = Id Zk

data CgIdInfo = CgIdInfo
  { cg_id :: CgId
  , cg_lf :: LambdaFormInfo
  , cg_loc :: CgLoc
  }

instance OutputableP Platform CgIdInfo where
  pdoc env CgIdInfo{ cg_id = id, cg_loc = loc }
    = ppr id <+> text "-->" <+> pdoc env loc

--------------------------------------------------------
--        The code generator state

data CgState = MkCgState
  { cgs_stmts :: PirAGraph
  , cgs_tops :: OrdList DPirDecl
  , cgs_binds :: CgBindings
  , cgs_uniqs :: UniqSupply
  }

data FCodeState = MkFCodeState
  { fcs_sequel :: !Sequel
  , fcs_selfloop :: !(Maybe SelfLoopInfo)
  }

initCgState :: UniqSupply -> CgState
initCgState uniqs = MkCgState
  { cgs_stmts = mkNop
  , cgs_tops = nilOL
  , cgs_binds = emptyVarEnv
  , cgs_uniqs = uniqs }

addCodeBlocksFrom :: CgState -> CgState -> CgState
addCodeBlocksFrom s1 s2
  = s1 { cgs_stmts = cgs_stmts s1 <:> cgs_stmts s2
       , cgs_tops = cgs_tops s1 `appOL` cgs_tops s2 }

--------------------------------------------------------
-- Operators for getting and setting the state
--------------------------------------------------------

getState :: FCode CgState
getState = FCode $ \_ _ state -> (state, state)

setState :: CgState -> FCode ()
setState state = FCode $ \_ _ _ -> ((), state)

withCgState :: FCode a -> CgState -> FCode (a, CgState)
withCgState (FCode fcode) newstate = FCode $ \cfg fstate state ->
  case fcode cfg fstate newstate of
    (retval, state2) -> ((retval, state2), state)
 
getBinds :: FCode CgBindings
getBinds = do
  state <- getState
  return $ cgs_binds state

setBinds :: CgBindings -> FCode ()
setBinds new_binds = do
  state <- getState
  setState $ state { cgs_binds = new_binds }

newUniqSupply :: FCode UniqSupply
newUniqSupply = do
  state <- getState
  let (us1, us2) = splitUniqSupply (cgs_uniqs state)
  setState $ state { cgs_uniqs = us1 }
  return us2

initFCodeState :: Platform -> FCodeState
initFCodeState p = MkFCodeState
  { fcs_sequel = Return
  , fcs_selfloop = Nothing
  }

getFCodeState :: FCode FCodeState
getFCodeState = FCode $ \_ fstate state -> (fstate, state)

withFCodeState :: FCode a -> FCodeState -> FCode a
withFCodeState (FCode fcode) fst = FCode $ \cfg _ state -> fcode cfg fst state

getSelfLoop :: FCode (Maybe SelfLoopInfo)
getSelfLoop = fcs_selfloop <$> getFCodeState

withSelfLoop :: SelfLoopInfo -> FCode a -> FCode a
withSelfLoop self_loop code = do
  fstate <- getFCodeState
  withFCodeState code (fstate { fcs_selfloop = Just self_loop })

-- ----------------------------------------------------------------------------
-- Config related helpers

getStgToPirConfig :: FCode StgToPirConfig
getStgToPirConfig = FCode $ \cfg _ state -> (cfg, state)

getProfile :: FCode Profile
getProfile = stgToPirProfile <$> getStgToPirConfig

getPlatform :: FCode Platform
getPlatform = profilePlatform <$> getProfile

getModuleName :: FCode Module
getModuleName = stgToPirThisModule <$> getStgToPirConfig

--------------------------------------------------------
--                 Forking
--------------------------------------------------------

forkFunctionBody :: FCode () -> FCode ()
forkFunctionBody body_code = do
  platform <- getPlatform
  cfg <- getStgToPirConfig
  fstate <- getFCodeState
  us <- newUniqSupply
  state <- getState
  let fcs = fstate { fcs_sequel = Return
                   , fcs_selfloop = Nothing
                   }
      fork_state_in = (initCgState us) { cgs_binds = cgs_binds state }
      ((), fork_state_out) = doFCode body_code cfg fcs fork_state_in
  setState $ state `addCodeBlocksFrom` fork_state_out

-- TODO: ticky stuff: tickScope, getTickScope, PirAGraphScoped
getCodeScoped :: FCode a -> FCode (a, PirAGraph)
getCodeScoped fcode = do
  state1 <- getState
  (a, state2) <-
    flip withCgState state1 { cgs_stmts = mkNop } $ do
      a <- fcode
      -- scp <- getTickScope
      return a
  setState $ state2 { cgs_stmts = cgs_stmts state1 }
  return (a, cgs_stmts state2)

-- ----------------------------------------------------------------------------
-- Combinators for emitting code

emitProc :: PLabel -> [PirFormal] -> PirAGraph -> FCode ()
emitProc lbl args blocks = do
  l <- newBlockId
  let blks :: DPirGraph
      blks = labelAGraph l blocks

      proc_lbl = toProcDelimiterLbl lbl

      proc_block = PirProc proc_lbl args blks

  state <- getState
  setState $ state { cgs_tops = cgs_tops state `snocOL` proc_block }

getPir :: FCode a -> FCode (a, DPirGroup)
getPir code = do
  state1 <- getState
  (a, state2) <- withCgState code (state1 { cgs_tops = nilOL })
  setState $ state2 { cgs_tops = cgs_tops state1 }
  return (a, fromOL (cgs_tops state2))
