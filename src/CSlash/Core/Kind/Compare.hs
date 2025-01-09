{-# LANGUAGE MagicHash #-}

module CSlash.Core.Kind.Compare where

import CSlash.Core.Kind

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
--    go :: RnEnv2 -> Kind -> Kind -> Bool
    go = panic "tcEqKind go"
    orig_env = panic "tcEqKind oe"
