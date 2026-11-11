{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE MagicHash #-}

module CSlash.Core.Kind.Compare where

import CSlash.Cs.Pass

import CSlash.Core.Kind
import CSlash.Core.Kind.FVs
import CSlash.Core.Type.FVs

import {-# SOURCE #-} CSlash.Types.Var.KiVar
import CSlash.Types.Var.Set
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


