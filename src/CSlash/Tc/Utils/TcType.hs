module CSlash.Tc.Utils.TcType
  ( TcType
  , TcTyVar

  , TcLevel(..)

  , TcTyVarDetails(..), pprTcTyVarDetails
  , MetaDetails, MetaInfo
  ) where

import Prelude hiding ((<>))

import CSlash.Core.Type.Rep
import CSlash.Types.Var
import CSlash.Core.TyCon

import {-# SOURCE #-} CSlash.Tc.Types.Origin
  ( SkolemInfo )

import CSlash.Types.Name as Name
import CSlash.Types.Name.Env
import CSlash.Types.Name.Set
import CSlash.Builtin.Names

import CSlash.Data.Maybe
import CSlash.Types.Basic
import CSlash.Utils.Misc
import CSlash.Utils.Outputable
import CSlash.Utils.Panic

import Data.IORef (IORef)

type TcType = Type

data TcTyVarDetails
  = SkolemTv SkolemInfo TcLevel
  | MetaTv { mtv_info :: MetaInfo
           , mtv_ref :: IORef MetaDetails
           , mtv_tclvl :: TcLevel
           }

instance Outputable TcTyVarDetails where
  ppr = pprTcTyVarDetails

pprTcTyVarDetails :: TcTyVarDetails -> SDoc
pprTcTyVarDetails (SkolemTv _sk lvl) = text "sk" <> colon <> ppr lvl
pprTcTyVarDetails (MetaTv { mtv_info = info, mtv_tclvl = tclvl })
  = ppr info <> colon <> ppr tclvl

data MetaDetails

data MetaInfo

instance Outputable MetaDetails

instance Outputable MetaInfo

newtype TcLevel = TcLevel Int deriving (Eq, Ord)

instance Outputable TcLevel where
  ppr (TcLevel us) = ppr us
