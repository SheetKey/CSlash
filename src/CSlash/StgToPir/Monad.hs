{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms #-}

module CSlash.StgToPir.Monad where

import CSlash.Cs.Pass
import CSlash.Platform
import CSlash.Platform.Profile
import CSlash.Pir
import CSlash.StgToPir.Config
import CSlash.StgToPir.Closure
-- import GHC.StgToCmm.Sequel
import CSlash.Pir.Graph as PirGraph
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

initCgState :: UniqSupply -> CgState
initCgState uniqs = MkCgState
  { cgs_stmts = mkNop
  , cgs_tops = nilOL
  , cgs_binds = emptyVarEnv
  , cgs_uniqs = uniqs }

--------------------------------------------------------
-- Operators for getting and setting the state
--------------------------------------------------------

getState :: FCode CgState
getState = FCode $ \_ _ state -> (state, state)

initFCodeState :: Platform -> FCodeState
initFCodeState p = MkFCodeState
