{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveDataTypeable #-}

module CSlash.Core.Type.Rep where

import {-# SOURCE #-} CSlash.Core.Type.Ppr (pprType)

import CSlash.Cs.Pass

import CSlash.Types.Var.TyVar
import CSlash.Types.Var.KiVar
import CSlash.Types.Var.CoVar
import CSlash.Types.Var.Class
import CSlash.Types.Var.Set
import CSlash.Core.TyCon
import CSlash.Core.Kind
import {-# SOURCE #-} CSlash.Core.Kind.Compare

import CSlash.Builtin.Names
import CSlash.Types.Name

import CSlash.Types.Basic (LeftOrRight(..), pickLR)
import CSlash.Utils.Outputable
import CSlash.Data.FastString
import CSlash.Utils.Misc
import CSlash.Utils.Panic
import CSlash.Utils.Binary
import CSlash.Utils.FV

import qualified Data.Data as Data hiding (TyCon)
import Data.IORef (IORef)
import Control.DeepSeq



