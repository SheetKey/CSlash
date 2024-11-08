module CSlash.Tc.Utils.TcType
  ( module CSlash.Tc.Utils.TcType
  , TcTyVar
  ) where

import Prelude hiding ((<>))

import CSlash.Core.Type.Rep
import CSlash.Types.Var
import CSlash.Core.TyCon

import {-# SOURCE #-} CSlash.Tc.Types.Origin
  ( SkolemInfo, unkSkol )

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

{- *********************************************************************
*                                                                      *
              Types
*                                                                      *
********************************************************************* -}

type TcType = Type

{- *********************************************************************
*                                                                      *
          ExpType: an "expected type" in the type checker
*                                                                      *
********************************************************************* -}

data ExpType
  = Check TcType
  | Infer !InferResult

data InferResult

{- *********************************************************************
*                                                                      *
        TyVarDetails, MetaDetails, MetaInfo
*                                                                      *
********************************************************************* -}

data TcTyVarDetails
  = SkolemTv SkolemInfo TcLevel
  | MetaTv { mtv_info :: MetaInfo
           , mtv_ref :: IORef MetaDetails
           , mtv_tclvl :: TcLevel
           }

vanillaSkolemTvUnk :: HasDebugCallStack => TcTyVarDetails
vanillaSkolemTvUnk = SkolemTv unkSkol topTcLevel

instance Outputable TcTyVarDetails where
  ppr = pprTcTyVarDetails

pprTcTyVarDetails :: TcTyVarDetails -> SDoc
pprTcTyVarDetails (SkolemTv _sk lvl) = text "sk" <> colon <> ppr lvl
pprTcTyVarDetails (MetaTv { mtv_info = info, mtv_tclvl = tclvl })
  = ppr info <> colon <> ppr tclvl

data MetaDetails
  = Flexi
  | Indirect TcType

data MetaInfo

instance Outputable MetaDetails where
  ppr = undefined

instance Outputable MetaInfo where
  ppr = undefined

{- *********************************************************************
*                                                                      *
                Untouchable type variables
*                                                                      *
********************************************************************* -}

newtype TcLevel = TcLevel Int deriving (Eq, Ord)

instance Outputable TcLevel where
  ppr (TcLevel us) = ppr us

topTcLevel :: TcLevel
topTcLevel = TcLevel 0
