module CSlash.Core.Opt.Coercion where

import CSlash.Cs.Pass

-- import CSlash.Tc.Utils.TcType   ( exactTyCoVarsOfType )

import CSlash.Core.Type.Rep
import CSlash.Core.Subst
import CSlash.Core.Type.Compare( eqType )
-- import GHC.Core.Coercion
import CSlash.Core.Type as Type hiding( substTyVarBndr, substTy )
import CSlash.Core.Kind
import CSlash.Core.TyCon
import CSlash.Core.Unify

import CSlash.Types.Basic( SwapFlag(..), flipSwap, isSwapped, pickSwap, notSwapped )
import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Types.Var.Env

import CSlash.Data.Pair

import CSlash.Utils.Outputable
import CSlash.Utils.Constants (debugIsOn)
import CSlash.Utils.Misc
import CSlash.Utils.Panic

import Control.Monad   ( zipWithM )

{- *********************************************************************
*                                                                      *
              Optimizing coercions
*                                                                      *
********************************************************************* -}

newtype OptCoercionOpts = OptCoercionOpts
  { optCoercionEnabled :: Bool
  }

optKiCoercion :: OptCoercionOpts -> CoreSubst -> KindCoercion Zk -> KindCoercion Zk
optKiCoercion opts env co
  | optCoercionEnabled opts
  = panic "optKiCoercion"
  | otherwise
  = substKiCo env co
