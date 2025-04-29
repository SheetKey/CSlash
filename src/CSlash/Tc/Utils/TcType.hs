module CSlash.Tc.Utils.TcType
  ( module CSlash.Tc.Utils.TcType
  , TcTyVar, TcKiVar
  ) where

import Prelude hiding ((<>))

import CSlash.Core.Type
import CSlash.Core.Type.Rep
import CSlash.Core.Type.FVs
import CSlash.Core.Kind
import CSlash.Core.Kind.FVs
import CSlash.Types.Var
import CSlash.Types.Var.Set
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
type TcTyConBinder = TyConBinder

type TcKind = Kind
type TcMonoKind = MonoKind
type TcPredKind = PredKind

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
  = TyVarTv

instance Outputable tk => Outputable (MetaDetails' tk) where
  ppr = panic "ppr metadetails'"

instance Outputable MetaInfo where
  ppr TyVarTv = text "tyv"

data TcKiVarDetails
  = SkolemKv SkolemInfo TcLevel
  | MetaKv { mkv_info :: MetaInfoK
           , mkv_ref :: IORef MetaDetailsK
           , mkv_tclvl :: TcLevel
           }

instance Outputable TcKiVarDetails where
  ppr = pprTcKiVarDetails

pprTcKiVarDetails :: TcKiVarDetails -> SDoc
pprTcKiVarDetails (SkolemKv _sk lvl) = text "sk" <> colon <> ppr lvl
pprTcKiVarDetails (MetaKv { mkv_info = info, mkv_tclvl = tclvl })
  = ppr info <> colon <> ppr tclvl

vanillaSkolemKvUnk :: HasDebugCallStack => TcKiVarDetails
vanillaSkolemKvUnk = SkolemKv unkSkol topTcLevel

type MetaDetailsK = MetaDetails' TcMonoKind

data MetaInfoK
  = KiVarKv
  | TauKv

instance Outputable MetaInfoK where
  ppr TauKv = text "tuakv"
  ppr KiVarKv = text "kiv"

data ConcreteKvOrigin

{- *********************************************************************
*                                                                      *
                Untouchable type variables
*                                                                      *
********************************************************************* -}

newtype TcLevel = TcLevel Int deriving (Eq, Ord)

instance Outputable TcLevel where
  ppr (TcLevel us) = ppr us

maxTcLevel :: TcLevel -> TcLevel -> TcLevel
maxTcLevel (TcLevel a) (TcLevel b) = TcLevel (a `max` b)

minTcLevel :: TcLevel -> TcLevel -> TcLevel
minTcLevel (TcLevel a) (TcLevel b) = TcLevel (a `min` b)

topTcLevel :: TcLevel
topTcLevel = TcLevel 0

pushTcLevel :: TcLevel -> TcLevel
pushTcLevel (TcLevel us) = TcLevel (us + 1)

strictlyDeeperThan :: TcLevel -> TcLevel -> Bool
strictlyDeeperThan (TcLevel lvl) (TcLevel ctxt_lvl) = lvl > ctxt_lvl

deeperThanOrSame :: TcLevel -> TcLevel -> Bool
deeperThanOrSame (TcLevel v_tclvl) (TcLevel ctxt_tclvl) = v_tclvl >= ctxt_tclvl

sameDepthAs :: TcLevel -> TcLevel -> Bool
sameDepthAs (TcLevel ctxt_tclvl) (TcLevel v_tclvl)
  = ctxt_tclvl == v_tclvl

checkTcLevelInvariant :: TcLevel -> TcLevel -> Bool
checkTcLevelInvariant (TcLevel ctxt_tclvl) (TcLevel v_tclvl)
  = ctxt_tclvl >= v_tclvl

tcVarLevel :: TcVar -> TcLevel
tcVarLevel v 
  | isTcTyVar v = tcTyVarLevel v
  | isTcKiVar v = tcKiVarLevel v
  | otherwise = pprPanic "tcVarLevel" (ppr v)

tcTyVarLevel :: TcTyVar -> TcLevel
tcTyVarLevel tv = case tcTyVarDetails tv of
  MetaTv { mtv_tclvl = tv_lvl } -> tv_lvl
  SkolemTv _ tv_lvl -> tv_lvl

tcKiVarLevel :: TcKiVar -> TcLevel
tcKiVarLevel kv = case tcKiVarDetails kv of
                    MetaKv { mkv_tclvl = kv_lvl } -> kv_lvl
                    SkolemKv _ kv_lvl -> kv_lvl

tcTypeLevel :: TcType -> TcLevel
tcTypeLevel ty = nonDetStrictFoldDVarSet add topTcLevel (tyKiVarsOfTypeDSet ty)
  where
    add v lvl
      | isTcTyVar v = lvl `maxTcLevel` tcTyVarLevel v
      | isTcKiVar v = lvl `maxTcLevel` tcKiVarLevel v
      | otherwise = lvl

tcMonoKindLevel :: TcMonoKind -> TcLevel
tcMonoKindLevel ki = nonDetStrictFoldDVarSet add topTcLevel (kiVarsOfMonoKindDSet ki)
  where
    add v lvl
      | isTcKiVar v = lvl `maxTcLevel` tcKiVarLevel v
      | otherwise = lvl

tcKindLevel :: TcKind -> TcLevel
tcKindLevel ki = nonDetStrictFoldDVarSet add topTcLevel (kiVarsOfKindDSet ki)
  where
    add v lvl
      | isTcKiVar v = lvl `maxTcLevel` tcKiVarLevel v
      | otherwise = lvl

{-# INLINE any_rewritable_ki #-}
any_rewritable_ki :: (TcKiVar -> Bool) -> TcMonoKind -> Bool
any_rewritable_ki kv_pred = go_mono emptyVarSet
  where
    go_mono :: VarSet -> TcMonoKind -> Bool
    go_mono bvs (KiConApp kc kis) = go_kc bvs kc kis
    go_mono bvs (KiVarKi kv) = go_kv bvs kv
    go_mono bvs (FunKi _ arg res) = go_mono bvs arg || go_mono bvs res

    go_kv bvs kv | kv `elemVarSet` bvs = False
                 | otherwise = kv_pred kv

    go_kc :: VarSet -> KiCon -> [TcMonoKind] -> Bool
    go_kc bvs _ kis = any (go_mono bvs) kis

anyRewritableKiVar :: (TcKiVar -> Bool) -> TcMonoKind -> Bool
anyRewritableKiVar = any_rewritable_ki

{- *********************************************************************
*                                                                      *
                Predicates
*                                                                      *
********************************************************************* -}

tcIsTcTyVar :: TcTyVar -> Bool
tcIsTcTyVar tv = isTyVar tv

tcIsTcKiVar :: TcKiVar -> Bool
tcIsTcKiVar kv = isKiVar kv

isPromotableMetaKiVar :: TcKiVar -> Bool
isPromotableMetaKiVar kv
  | isKiVar kv
  , MetaKv { mkv_info = info } <- tcKiVarDetails kv
  = isTouchableInfoK info
  | otherwise
  = False

isTouchableMetaKiVar :: TcLevel -> TcKiVar -> Bool
isTouchableMetaKiVar ctxt_tclvl kv
  | isKiVar kv
  , MetaKv { mkv_tclvl = kv_tclvl, mkv_info = info } <- tcKiVarDetails kv
  , isTouchableInfoK info
  = assertPpr (checkTcLevelInvariant ctxt_tclvl kv_tclvl)
              (ppr kv $$ ppr kv_tclvl $$ ppr ctxt_tclvl)
    $ kv_tclvl `sameDepthAs` ctxt_tclvl
  | otherwise = False

isImmutableTyVar :: TypeVar -> Bool
isImmutableTyVar tv = isSkolemTyVar tv

isImmutableKiVar :: KindVar -> Bool
isImmutableKiVar tv = isSkolemKiVar tv

isSkolemTyVar :: TcTyVar -> Bool
isSkolemTyVar tv = assertPpr (tcIsTcTyVar tv) (ppr tv)
  $ case tcTyVarDetails tv of
      MetaTv {} -> False
      _ -> True

isSkolemKiVar :: TcKiVar -> Bool
isSkolemKiVar kv = assertPpr (tcIsTcKiVar kv) (ppr kv)
  $ case tcKiVarDetails kv of
      MetaKv {} -> False
      _ -> True

isMetaTyVar :: TypeVar -> Bool
isMetaTyVar tv
  | isTyVar tv
  = case tcTyVarDetails tv of
      MetaTv {} -> True
      _ -> False
  | otherwise
  = False

isMetaKiVar :: TcKiVar -> Bool
isMetaKiVar kv
  | isKiVar kv
  = case tcKiVarDetails kv of
      MetaKv {} -> True
      _ -> False
  | otherwise = False

isConcreteKiVar_maybe :: TcKiVar -> Maybe (TcKiVar, ConcreteKvOrigin)
isConcreteKiVar_maybe kv
  | isTcKiVar kv
  , MetaKv { mkv_info = info } <- tcKiVarDetails kv
  = case info of
      KiVarKv -> Nothing
      TauKv -> Nothing
  | otherwise
  = Nothing

isConcreteInfoK :: MetaInfoK -> Bool
isConcreteInfoK KiVarKv = False
isConcreteInfoK TauKv = False

isConcreteKiVar :: TcKiVar -> Bool
isConcreteKiVar = isJust . isConcreteKiVar_maybe

isTouchableInfoK :: MetaInfoK -> Bool
isTouchableInfoK _info = True

metaTyVarRef :: TypeVar -> IORef MetaDetails
metaTyVarRef tv = case tcTyVarDetails tv of
                    MetaTv { mtv_ref = ref } -> ref
                    _ -> pprPanic "metaTyVarRef" (ppr tv)

metaKiVarRef :: KindVar -> IORef MetaDetailsK
metaKiVarRef kv = case tcKiVarDetails kv of
                    MetaKv { mkv_ref = ref } -> ref
                    _ -> pprPanic "metaKiVarRef" (ppr kv)

setMetaKiVarTcLevel :: TcKiVar -> TcLevel -> TcKiVar
setMetaKiVarTcLevel kv tclvl = case tcKiVarDetails kv of
                                 details@(MetaKv {})
                                   -> setTcKiVarDetails kv (details { mkv_tclvl = tclvl })
                                 _ -> pprPanic "metaKiVarTcLevel" (ppr kv)

isTyVarTyVar :: Var -> Bool
isTyVarTyVar tv
  | isTcTyVar tv
  = case tcTyVarDetails tv of
      MetaTv { mtv_info = TyVarTv } -> True
      _ -> False
  | otherwise
  = False

isKiVarKiVar :: Var -> Bool
isKiVarKiVar kv
  | isTcKiVar kv
  = case tcKiVarDetails kv of
      MetaKv { mkv_info = KiVarKv } -> True
      _ -> False
  | otherwise
  = False

isFlexi :: MetaDetails' tk -> Bool
isFlexi Flexi = True
isFlexi _ = False

mkKiVarNamePairs :: [KindVar] -> [(Name, KindVar)]
mkKiVarNamePairs kvs = [(kiVarName kv, kv) | kv <- kvs ]

{- *********************************************************************
*                                                                      *
          Expanding and splitting kinds
*                                                                      *
********************************************************************* -}

tcSplitFunKi_maybe :: Kind -> Maybe (FunKiFlag, MonoKind, MonoKind)
tcSplitFunKi_maybe = splitFunKi_maybe

tcSplitMonoFunKi_maybe :: MonoKind -> Maybe (FunKiFlag, MonoKind, MonoKind)
tcSplitMonoFunKi_maybe = splitMonoFunKi_maybe

tcSplitForAllKi_maybe :: Kind -> Maybe (KindVar, Kind)
tcSplitForAllKi_maybe = splitForAllKi_maybe

tcSplitPiKi_maybe :: Kind -> Maybe (Either (KindVar, Kind) (FunKiFlag, MonoKind, MonoKind))
tcSplitPiKi_maybe ki = assert (isMaybeKiBinder ski) ski
  where
    ski = splitPiKi_maybe ki

    isMaybeKiBinder (Just (Left (kv, _))) = isKiVar kv
    isMaybeKiBinder _ = True

{- *********************************************************************
*                                                                      *
          Expanding and splitting 
*                                                                      *
********************************************************************* -}

tcSplitForAllTyVarBinders :: Type -> ([TyVarBinder], Type)
tcSplitForAllTyVarBinders ty = assert (all isTyVarBinder (fst sty)) sty
  where sty = splitForAllForAllTyBinders ty

tcSplitTyLamTyVarBinders :: Type -> ([TypeVar], Type)
tcSplitTyLamTyVarBinders ty = assert (all isTyVar (fst sty)) sty
  where sty = splitTyLamTyBinders ty

tcSplitBigLamTyVarBinders :: Type -> ([KindVar], Type)
tcSplitBigLamTyVarBinders ty = assert (all isKiVar (fst sty)) sty
  where sty = splitBigLamTyBinders ty
