module CSlash.Core.Kind where

import CSlash.Types.Var

{- **********************************************************************
*                                                                       *
                        Kind
*                                                                       *
********************************************************************** -}

type Mult = Kind

data Kind
  = KdVarKd Var
  | UKd
  | AKd
  | LKd
  | FunKd
    { kft_arg :: Kind
    , kft_res :: Kind
    }
  | LTKd Kind Kind
  | LTEQKd Kind Kind

