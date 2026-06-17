module CSlash.Builtin.PrimOps where

data PrimOp
  = DoubleToFloatOp
  | FloatToDoubleOp
  | IntToInt Int Int
  | IntToUInt Int Int
  | UIntToInt Int Int
  | UIntToUInt Int Int
  | Int64ToAddrOp
  | AddrToInt64Op
