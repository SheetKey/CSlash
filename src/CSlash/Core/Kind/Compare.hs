{-# LANGUAGE MagicHash #-}

module CSlash.Core.Kind.Compare where

import CSlash.Core.Kind
import CSlash.Core.Kind.FVs

import CSlash.Core.Type.Rep
import CSlash.Core.Type.FVs
import CSlash.Core.TyCon

import CSlash.Types.Var
import CSlash.Types.Unique
import CSlash.Types.Var.Env

import CSlash.Utils.Outputable
import CSlash.Utils.Misc
import CSlash.Utils.Panic

import GHC.Base (reallyUnsafePtrEquality#)

import qualified Data.Semigroup as S

{- *********************************************************************
*                                                                      *
            Kind equality
*                                                                      *
********************************************************************* -}

tcEqKind :: HasDebugCallStack => Kind -> Kind -> Bool
tcEqKind orig_ki1 orig_ki2 = go orig_env orig_ki1 orig_ki2
  where
    go :: RnEnv2 -> Kind -> Kind -> Bool
    go _ UKd UKd = True
    go _ AKd AKd = True
    go _ LKd LKd = True
    go env (KiVarKi kv1) (KiVarKi kv2)
      = rnOccL env kv1 == rnOccR env kv2
    go env (FunKd _ arg1 res1) (FunKd _ arg2 res2)
      = go env arg1 arg2 && go env res1 res2
    go env (KdContext rels1) (KdContext rels2)
      = all2 (go_rel env) rels1 rels2
    go _ _ _ = False

    go_rel env (LTKd k1 k2) (LTKd k1' k2')
      = go env k1 k1' && go env k2 k2'
    go_rel env (LTEQKd k1 k2) (LTEQKd k1' k2')
      = go env k1 k1' && go env k2 k2'
    go_rel _ _ _ = False

    orig_env = mkRnEnv2 $ mkInScopeSet $ kiVarsOfKinds [orig_ki1, orig_ki2]
