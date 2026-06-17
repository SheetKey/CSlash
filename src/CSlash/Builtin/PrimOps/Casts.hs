module CSlash.Builtin.PrimOps.Casts (getCasts) where

import CSlash.Cs.Pass
import CSlash.Core.TyCon
import CSlash.Utils.Outputable
import CSlash.Utils.Panic
import CSlash.Utils.Misc (HasDebugCallStack)
import CSlash.Types.RepType
import CSlash.Core.Type
import CSlash.Builtin.Types.Prim

import CSlash.Builtin.PrimOps

getCasts :: PrimRep -> PrimRep -> [(PrimOp, Type Zk)]
getCasts from_rep to_rep
  | to_rep == from_rep
  = []

  -- Float <-> Double
  | to_rep == FloatRep
  = assertPpr (from_rep == DoubleRep) (ppr from_rep <+> ppr to_rep) $
    [(DoubleToFloatOp, floatPrimTy_U)]
  | to_rep == DoubleRep
  = assertPpr (from_rep == FloatRep) (ppr from_rep <+> ppr to_rep) $
    [(FloatToDoubleOp, doublePrimTy_U)]

  -- Addr <-> UInt/Int
  | to_rep == AddrRep = uintOrIntToAddrRep from_rep
  | from_rep == AddrRep = addrToUIntOrIntRep to_rep

  -- Int* -> Int*
  | IntRep f <- from_rep
  , IntRep t <- to_rep
  = intToIntRep f t

  -- UInt* -> UInt*
  | UIntRep f <- from_rep
  , UIntRep t <- to_rep
  = uintToUIntRep f t

  -- UInt* -> Int*
  | UIntRep f <- from_rep
  , IntRep t <- to_rep
  = uintToIntRep f t

  -- Int* -> UInt*
  | IntRep f <- from_rep
  , UIntRep t <- to_rep
  = intToUIntRep f t

  | otherwise = pprPanic "getCasts:Unexpected rep combination" (ppr (from_rep, to_rep))

uintOrIntToAddrRep :: HasDebugCallStack => PrimRep -> [(PrimOp, Type Zk)]
uintOrIntToAddrRep AddrRep = []
uintOrIntToAddrRep (IntRep 64) = [(Int64ToAddrOp, addrPrimTy_U)]
uintOrIntToAddrRep (IntRep i)
  = intToIntRep i 64 ++ [(Int64ToAddrOp, addrPrimTy_U)]
uintOrIntToAddrRep (UIntRep i)
  = uintToIntRep i 64 ++ [(Int64ToAddrOp, addrPrimTy_U)]
uintOrIntToAddrRep rep = pprPanic "Rep not uint or int rep" (ppr rep)

addrToUIntOrIntRep :: HasDebugCallStack => PrimRep -> [(PrimOp, Type Zk)]
addrToUIntOrIntRep (IntRep 64) = [(AddrToInt64Op, intPrimTy_U 64)]
addrToUIntOrIntRep (IntRep i)
  = (AddrToInt64Op, intPrimTy_U 64) : intToIntRep 64 i
addrToUIntOrIntRep (UIntRep i)
  = (AddrToInt64Op, intPrimTy_U 64) : intToUIntRep 64 i
addrToUIntOrIntRep rep = pprPanic "Target rep not uint or int rep" (ppr rep)

uintToIntRep :: Int -> Int -> [(PrimOp, Type Zk)]
uintToIntRep from to = [(UIntToInt from to, intPrimTy_U to)]

intToUIntRep :: Int -> Int -> [(PrimOp, Type Zk)]
intToUIntRep from to = [(IntToUInt from to, uintPrimTy_U to)]

intToIntRep :: Int -> Int -> [(PrimOp, Type Zk)]
intToIntRep from to
  | from == to
  = []
  | otherwise
  = [(IntToInt from to, intPrimTy_U to)]

uintToUIntRep :: Int -> Int -> [(PrimOp, Type Zk)]
uintToUIntRep from to
  | from == to
  = []
  | otherwise
  = [(UIntToUInt from to, uintPrimTy_U to)]

intPrimTy_U :: Int -> Type Zk
intPrimTy_U = panic "intPrimTy_U"

uintPrimTy_U :: Int -> Type Zk
uintPrimTy_U = panic "uintPrimTy_U"

floatPrimTy_U :: Type Zk
floatPrimTy_U = panic "intPrimTy_U"

doublePrimTy_U :: Type Zk
doublePrimTy_U = panic "intPrimTy_U"

addrPrimTy_U :: Type Zk
addrPrimTy_U = panic "intPrimTy_U"
