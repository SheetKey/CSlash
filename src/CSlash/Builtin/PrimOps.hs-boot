module CSlash.Builtin.PrimOps where

data PrimOp
  -- Casts
  = IntToInt Int Int
  | IntToUInt Int Int
  | UIntToInt Int Int
  | UIntToUInt Int Int
  | DoubleToFloatOp 
  | FloatToDoubleOp 
  | Int64ToAddrOp
  | AddrToInt64Op

  -- IO
  | ReturnIO
  | BindIO
