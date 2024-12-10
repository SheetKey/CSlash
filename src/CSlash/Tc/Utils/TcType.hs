module CSlash.Tc.Utils.TcType
  ( module CSlash.Tc.Utils.TcType
  , TcTyVar, TcKiVar
  ) where

import Prelude hiding ((<>))

import CSlash.Core.Type.Rep
import CSlash.Core.Kind
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

type TcTyVarBinder = TyVarBinder

type TcTyCon = TyCon
type MonoTcTyCon = TcTyCon
type PolyTcTyCon = TcTyCon

type TcKind = Kind

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

data MetaDetails' tk
  = Flexi
  | Indirect tk

type MetaDetails = MetaDetails' TcType

data MetaInfo

instance Outputable tk => Outputable (MetaDetails' tk) where
  ppr = undefined

instance Outputable MetaInfo where
  ppr = undefined

data TcKiVarDetails
  = SkolemKv SkolemInfo TcLevel
  | MetaKv { mkv_info :: MetaInfoK
           , mkv_ref :: IORef MetaDetailsK
           , mkv_tclvl :: TcLevel
           }

vanillaSkolemKvUnk :: HasDebugCallStack => TcKiVarDetails
vanillaSkolemKvUnk = SkolemKv unkSkol topTcLevel

type MetaDetailsK = MetaDetails' TcKind

data MetaInfoK
  = KiVarKind
  | TauKv

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

pushTcLevel :: TcLevel -> TcLevel
pushTcLevel (TcLevel us) = TcLevel (us + 1)

strictlyDeeperThan :: TcLevel -> TcLevel -> Bool
strictlyDeeperThan (TcLevel lvl) (TcLevel ctxt_lvl) = lvl > ctxt_lvl

deeperThanOrSame :: TcLevel -> TcLevel -> Bool
deeperThanOrSame (TcLevel v_tclvl) (TcLevel ctxt_tclvl) = v_tclvl >= ctxt_tclvl

tcKiVarLevel :: TcKiVar -> TcLevel
tcKiVarLevel kv = case tcKiVarDetails kv of
                    MetaKv { mkv_tclvl = kv_lvl } -> kv_lvl
                    SkolemKv _ kv_lvl -> kv_lvl

tcKindLevel :: TcKind -> TcLevel
tcKindLevel ki = panic "tcKindLevel"

{- *********************************************************************
*                                                                      *
                Predicates
*                                                                      *
********************************************************************* -}

isPromotableMetaKiVar :: TcKiVar -> Bool
isPromotableMetaKiVar kv
  | isKiVar kv
  , MetaKv { mkv_info = info } <- tcKiVarDetails kv
  = isTouchableInfoK info
  | otherwise
  = False

isMetaKiVar :: TcKiVar -> Bool
isMetaKiVar kv
  | isKiVar kv
  = case tcKiVarDetails kv of
      MetaKv {} -> True
      _ -> False
  | otherwise = False

isTouchableInfoK :: MetaInfoK -> Bool
isTouchableInfoK _info = True

metaKiVarRef :: KindVar -> IORef MetaDetailsK
metaKiVarRef kv = case tcKiVarDetails kv of
                    MetaKv { mkv_ref = ref } -> ref
                    _ -> pprPanic "metaKiVarRef" (ppr kv)

setMetaKiVarTcLevel :: TcKiVar -> TcLevel -> TcKiVar
setMetaKiVarTcLevel kv tclvl = case tcKiVarDetails kv of
                                 details@(MetaKv {})
                                   -> setTcKiVarDetails kv (details { mkv_tclvl = tclvl })
                                 _ -> pprPanic "metaKiVarTcLevel" (ppr kv)

isFlexi :: MetaDetails' tk -> Bool
isFlexi Flexi = True
isFlexi _ = False

mkKiVarNamePairs :: [KindVar] -> [(Name, KindVar)]
mkKiVarNamePairs kvs = [(kiVarName kv, kv) | kv <- kvs ]

{- *********************************************************************
*                                                                      *
          Expanding and splitting
*                                                                      *
********************************************************************* -}

tcSplitFunKi_maybe :: Kind -> Maybe (Kind, Kind)
tcSplitFunKi_maybe = splitFunKi_maybe
