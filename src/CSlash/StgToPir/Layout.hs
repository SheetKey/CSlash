module CSlash.StgToPir.Layout where

import CSlash.StgToPir.Function
import CSlash.StgToPir.Env
-- import CSlash.StgToCmm.ArgRep -- notably: ( slowCallPattern )
-- import GHC.StgToCmm.Ticky
import CSlash.StgToPir.Monad
-- import GHC.StgToCmm.Lit
-- import GHC.StgToCmm.Utils

import CSlash.Pir.Graph
-- import GHC.Runtime.Heap.Layout
import CSlash.Pir.BlockId
import CSlash.Pir
-- import CSlash.Pir.Utils
-- import CSlash.Pir.Info
import CSlash.Pir.PLabel
import CSlash.Stg.Syntax
import CSlash.Types.Var.Id
import CSlash.Core.TyCon ( PrimRep(..), PrimOrVoidRep(..){-, primRepSizeB-} )
import CSlash.Types.Basic ( RepArity )
import CSlash.Platform
import CSlash.Platform.Profile
import CSlash.Unit

import CSlash.Utils.Misc
import Data.List (mapAccumL, partition)
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Constants (debugIsOn)
import CSlash.Data.FastString
import Control.Monad
import CSlash.StgToPir.Config (stgToPirPlatform)
import CSlash.StgToPir.Types

------------------------------------------------------------------------
--                Call and return sequences
------------------------------------------------------------------------

emitReturn :: [PirExpr] -> FCode ()
emitReturn results = do
  profile <- getProfile
  platform <- getPlatform
  sequel <- getSequel
  case sequel of
    Return -> do
      emit $ mkReturn profile results

emitCall :: PirExpr -> [PirExpr] -> FCode ()
emitCall fun args = do
  profile <- getProfile
  sequel <- getSequel
  case sequel of
    Return -> do
      emit $ mkJump profile fun args
      return ()

-------------------------------------------------------------------------
--        Making calls: directCall and slowCall
-------------------------------------------------------------------------

directCall :: PLabel -> RepArity -> [StgArg] -> FCode ()
directCall lbl arity stg_args = do
  argreps <- getArgRepsAmodes stg_args
  direct_call "directCall" lbl arity argreps

direct_call :: String -> PLabel -> RepArity -> [Maybe PirExpr] -> FCode ()
direct_call caller lbl arity args
  | debugIsOn && args `lengthLessThan` arity
  = panic "direct_call not enough args"

  | null rest_args
  = emitCall target (nonVArgs args)

  | otherwise
  = panic "direct_call has extra args"

  where
    target = PirLit (PirLabel lbl)
    (fast_args, rest_args) = splitAt arity args

getArgRepsAmodes :: [StgArg] -> FCode [Maybe PirExpr]
getArgRepsAmodes args = do
  platform <- profilePlatform <$> getProfile
  mapM (getArgRepAmode platform) args
  where
    getArgRepAmode platform arg = case stgArgRep1 arg of
      VoidRep -> return Nothing
      NVRep _ -> do expr <- getArgAmode (NonVoid arg)
                    return (Just expr)

nonVArgs :: [Maybe PirExpr] -> [PirExpr] 
nonVArgs [] = []
nonVArgs (Nothing : args) = nonVArgs args
nonVArgs (Just arg : args) = arg : nonVArgs args
