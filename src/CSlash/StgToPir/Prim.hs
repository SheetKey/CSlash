{-# LANGUAGE LambdaCase #-}

module CSlash.StgToPir.Prim (cgOpApp{-, shouldInlinePrimOp-}) where

import CSlash.Platform
import CSlash.Platform.Profile

import CSlash.StgToPir.Config
import CSlash.StgToPir.Layout
-- import GHC.StgToPir.Foreign
import CSlash.StgToPir.Monad
import CSlash.StgToPir.Env
-- import GHC.StgToPir.Utils
-- import GHC.StgToPir.Ticky
-- import GHC.StgToPir.Heap
-- import GHC.StgToPir.Prof ( costCentreFrom )

import CSlash.Types.Basic
import CSlash.Types.RepType
import CSlash.Pir.BlockId
import CSlash.Pir.Graph
import CSlash.Stg.Syntax
import CSlash.Pir
-- import GHC.Unit         ( rtsUnit )
import CSlash.Core.Type ( Type, tyConAppTyCon_maybe )
import CSlash.Core.TyCon
import CSlash.Pir.PLabel
-- import GHC.Cmm.Info ( closureInfoPtr )
-- import CSlash.Pir.Utils
import CSlash.Builtin.PrimOps
-- import GHC.Runtime.Heap.Layout
import CSlash.Data.FastString
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import Data.Maybe

import Control.Monad (liftM, when, unless, zipWithM_)
import CSlash.Utils.Outputable

------------------------------------------------------------------------
--      Primitive operations and foreign calls
------------------------------------------------------------------------

cgOpApp :: StgOp -> [StgArg] -> CoreType -> FCode ()
cgOpApp (StgPrimOp primop) args res_ty = do
  cfg <- getStgToPirConfig
  pir_args <- getNonVoidArgAmodes args
  pirPrimOpApp cfg primop pir_args (Just res_ty)

pirPrimOpApp :: StgToPirConfig -> PrimOp -> [PirExpr] -> Maybe CoreType -> FCode ()
pirPrimOpApp cfg primop pir_args mres_ty = case emitPrimOp cfg primop pir_args of
  PrimopPirEmit_Internal f ->
    let res_ty = fromMaybe (primOpResultType primop) mres_ty
    in f res_ty >>= emitReturn

------------------------------------------------------------------------
--      Emitting code for a primop
------------------------------------------------------------------------

emitPrimOp
  :: StgToPirConfig
  -> PrimOp
  -> [PirExpr]
  -> PrimopPirEmit
emitPrimOp cfg primop =
  let max_inl_alloc_size = fromIntegral (stgToPirMaxInlAllocSize cfg)
  in case primop of
    ReturnIO -> \case [] -> PrimopPirEmit_Internal $ \_ -> return []
                      args -> opNop args
    BindIO -> panic "BindIO"

    -- Casts
    -- DoubleToFloatOp 
    -- FloatToDoubleOp 
    -- Int64ToAddrOp
    -- AddrToInt64Op
    -- IntToInt Int Int
    -- IntToUInt Int Int
    -- UIntToInt Int Int
    -- UIntToUInt Int Int

    other -> pprPanic "emitPrimOp other" (text (show other))
  where
    profile = stgToPirProfile cfg
    platform = stgToPirPlatform cfg
    result_info = getPrimOpResultInfo primop

    opNop :: [PirExpr] -> PrimopPirEmit
    opNop args = opIntoRegs $ \[res] -> emitAssign res arg
      where [arg] = args

    opIntoRegs :: ([LocalReg] -> FCode ()) -> PrimopPirEmit
    opIntoRegs f = PrimopPirEmit_Internal $ \res_ty -> do
      regs <- case result_info of
        ReturnsVoid -> ret_void
        ReturnsPrim rep -> ret_prim rep
        ReturnsTuple -> panic "returns tuple"
        ReturnsPoly -> case typePrimRep res_ty of
          [] -> ret_void
          [rep] -> ret_prim rep
          many -> panic "returns tuple"
      f regs
      pure $ map PirReg regs
      where
        ret_void = pure []
        ret_prim = panic "ret_prim"

data PrimopPirEmit
  = PrimopPirEmit_Internal (CoreType -> FCode [PirExpr])
