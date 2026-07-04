module CSlash.Builtin.PrimOps where

data PrimOp
  -- IO
  = ReturnIO
  | BindIO

  -- Casts
  | DoubleToFloatOp 
  | FloatToDoubleOp 
  | Int64ToAddrOp
  | AddrToInt64Op
  | IntToInt Int Int
  | IntToUInt Int Int
  | UIntToInt Int Int
  | UIntToUInt Int Int
