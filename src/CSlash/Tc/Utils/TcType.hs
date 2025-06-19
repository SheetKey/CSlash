{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CSlash.Tc.Utils.TcType
  ( module CSlash.Tc.Utils.TcType
  , TcTyVar, TcKiVar
  ) where

import Prelude hiding ((<>))

import CSlash.Core.Type
import CSlash.Core.Type.Rep
import CSlash.Core.Type.FVs
import CSlash.Core.Kind
import CSlash.Core.Kind.Compare
import CSlash.Core.Kind.FVs
import CSlash.Types.Var
import CSlash.Types.Var.Set
import CSlash.Core.TyCon
import CSlash.Core.Predicate

import {-# SOURCE #-} CSlash.Tc.Types.Origin
  ( SkolemInfo, unkSkol )

import CSlash.Types.Name as Name hiding (varName)
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

type AnyType = Type (AnyTyVar AnyKiVar) AnyKiVar
type TcType = Type (TcTyVar TcKiVar) TcKiVar

type AnyTyVarBinder = VarBndr (AnyTyVar AnyKiVar) ForAllFlag
type TcTyVarBinder = VarBndr (TcTyVar TcKiVar) ForAllFlag

type MonoAnyTyCon = AnyTyCon
type PolyAnyTyCon = AnyTyCon
type MonoTcTyCon = TcTyCon
type PolyTcTyCon = TcTyCon

type AnyKind = Kind AnyKiVar
type AnyMonoKind = MonoKind AnyKiVar
type AnyPredKind = PredKind AnyKiVar

type TcKind = Kind TcKiVar
type TcMonoKind = MonoKind TcKiVar
type TcPredKind = PredKind TcKiVar

type TcKindCoercion = KindCoercion (TcTyVar TcKiVar) TcKiVar
type AnyKindCoercion = KindCoercion (AnyTyVar AnyKiVar) AnyKiVar

type TcKindCoercionHole = KindCoercionHole (TcTyVar TcKiVar) TcKiVar
type AnyKindCoercionHole = KindCoercionHole (AnyTyVar AnyKiVar) AnyKiVar

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

data TcVarDetails tyki
  = SkolemVar SkolemInfo TcLevel
  | MetaVar { mv_info :: MetaInfo
            , mv_ref :: IORef (MetaDetails tyki)
            , mv_tclvl :: TcLevel
            }

data MetaDetails tk
  = Flexi
  | Indirect tk

data MetaInfo
  = TauVar
  | VarVar

instance Outputable (TcVarDetails tk) where
  ppr = pprTcVarDetails

pprTcVarDetails :: TcVarDetails tk -> SDoc
pprTcVarDetails (SkolemVar _sk lvl) = text "sk" <> colon <> ppr lvl
pprTcVarDetails (MetaVar { mv_info = info, mv_tclvl = tclvl })
  = ppr info <> colon <> ppr tclvl

instance Outputable tk => Outputable (MetaDetails tk) where
  ppr = panic "ppr metadetails'"

instance Outputable MetaInfo where
  ppr TauVar = text "tau"
  ppr VarVar = text "var"

vanillaSkolemVarUnk :: HasDebugCallStack => TcVarDetails tk
vanillaSkolemVarUnk = SkolemVar unkSkol topTcLevel

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

isTopTcLevel :: TcLevel -> Bool
isTopTcLevel (TcLevel 0) = True
isTopTcLevel _ = False

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

varLevel :: TcVar v => v -> TcLevel
varLevel v = case tcVarDetails v of
  MetaVar { mv_tclvl = tc_lvl } -> tc_lvl
  SkolemVar _ tc_lvl -> tc_lvl

-- tcTyVarLevel :: TcTyVar -> TcLevel
-- tcTyVarLevel tv = case tcTyVarDetails tv of
--   MetaTv { mtv_tclvl = tv_lvl } -> tv_lvl
--   SkolemTv _ tv_lvl -> tv_lvl

-- tcKiVarLevel :: TcKiVar -> TcLevel
-- tcKiVarLevel kv = case tcKiVarDetails kv of
--   MetaKv { mkv_tclvl = kv_lvl } -> kv_lvl
--   SkolemKv _ kv_lvl -> kv_lvl

anyTypeLevel :: AnyType -> TcLevel
anyTypeLevel ty = tenv_lvl `maxTcLevel` kenv_lvl
  where
    (tenv, kenv) = varsOfTypeDSet ty
    tenv_lvl = nonDetStrictFoldDVarSet (handleAnyTv
                                        (const $ \lvl -> lvl `maxTcLevel` topTcLevel)
                                        add) topTcLevel tenv
    kenv_lvl = nonDetStrictFoldDVarSet (handleAnyKv
                                        (const $ \lvl -> lvl `maxTcLevel` topTcLevel)
                                        add) topTcLevel kenv

    add :: TcVar v => v -> TcLevel -> TcLevel
    add v lvl = lvl `maxTcLevel` varLevel v

tcTypeLevel :: TcType -> TcLevel
tcTypeLevel ty = tenv_lvl `maxTcLevel` kenv_lvl
  where
    (tenv, kenv) = varsOfTypeDSet ty
    tenv_lvl = nonDetStrictFoldDVarSet add topTcLevel tenv
    kenv_lvl = nonDetStrictFoldDVarSet add topTcLevel kenv

    add :: TcVar v => v -> TcLevel -> TcLevel
    add v lvl = lvl `maxTcLevel` varLevel v

anyMonoKindLevel :: AnyMonoKind -> TcLevel
anyMonoKindLevel ki = nonDetStrictFoldDVarSet add topTcLevel (varsOfMonoKindDSet ki)
  where
    add = handleAnyKv (const $ \lvl -> lvl `maxTcLevel` topTcLevel) addTc
    addTc v lvl = lvl `maxTcLevel` varLevel v

tcMonoKindLevel :: TcMonoKind -> TcLevel
tcMonoKindLevel ki = nonDetStrictFoldDVarSet add topTcLevel (varsOfMonoKindDSet ki)
  where
    add v lvl = lvl `maxTcLevel` varLevel v

tcKindLevel :: AnyKind -> TcLevel
tcKindLevel ki = nonDetStrictFoldDVarSet add topTcLevel (varsOfKindDSet ki)
  where
    add = handleAnyKv (const $ \lvl -> lvl `maxTcLevel` topTcLevel) addTc
    addTc v lvl = lvl `maxTcLevel` varLevel v

{-# INLINE any_rewritable_ki #-}
any_rewritable_ki :: (TcKiVar -> Bool) -> AnyMonoKind -> Bool
any_rewritable_ki kv_pred = go_mono emptyVarSet
  where
    go_mono :: MkVarSet AnyKiVar -> AnyMonoKind -> Bool
    go_mono bvs (KiConApp kc kis) = go_kc bvs kc kis
    go_mono bvs (KiVarKi kv) = go_kv bvs kv
    go_mono bvs (FunKi _ arg res) = go_mono bvs arg || go_mono bvs res

    go_kv bvs kv | kv `elemVarSet` bvs = False
                 | otherwise = handleAnyKv (const False) kv_pred kv

    go_kc :: MkVarSet AnyKiVar -> KiCon -> [AnyMonoKind] -> Bool
    go_kc bvs _ kis = any (go_mono bvs) kis

anyRewritableKiVar :: (TcKiVar -> Bool) -> AnyMonoKind -> Bool
anyRewritableKiVar = any_rewritable_ki

{- *********************************************************************
*                                                                      *
                Predicates
*                                                                      *
********************************************************************* -}

isPromotableMetaVar :: TcVar v => v -> Bool
isPromotableMetaVar v = case tcVarDetails v of
   MetaVar { mv_info = info } -> isTouchableInfo info
   _ -> False

isTouchableMetaVar :: TcVar v => TcLevel -> v -> Bool
isTouchableMetaVar ctxt_tclvl v = case tcVarDetails v of
  MetaVar { mv_tclvl = tclvl, mv_info = info }
    | isTouchableInfo info
      ->  assertPpr (checkTcLevelInvariant ctxt_tclvl tclvl)
          (text "isTouchableMetaVar" $$ ppr tclvl $$ ppr ctxt_tclvl)
          $ tclvl `sameDepthAs` ctxt_tclvl
  _ -> False

isImmutableVar :: TcVar v => v -> Bool
isImmutableVar v = isSkolemVar v

isSkolemVar :: TcVar v => v -> Bool
isSkolemVar v = case tcVarDetails v of
  MetaVar {} -> False
  _ -> True

isMetaVar :: TcVar v => v -> Bool
isMetaVar v = case tcVarDetails v of
                MetaVar {} -> True
                _ -> False

isAmbiguousVar :: TcVar v => v -> Bool
isAmbiguousVar v = case tcVarDetails v of
  MetaVar {} -> True
  _ -> False

isConcreteVar_maybe :: TcVar v => v -> Maybe ConcreteKvOrigin
isConcreteVar_maybe kv 
  | MetaVar { mv_info = info } <- tcVarDetails kv
  = case info of
      VarVar -> Nothing
      TauVar -> Nothing
  | otherwise
  = Nothing

isConcreteKiVarKi_maybe :: AnyMonoKind -> Maybe (TcKiVar, ConcreteKvOrigin)
isConcreteKiVarKi_maybe (KiVarKi kv)
  = handleAnyKv (const Nothing) (\kv -> (kv, ) <$> isConcreteVar_maybe kv) kv
isConcreteKiVarKi_maybe _ = Nothing

isConcreteInfo :: MetaInfo -> Bool
isConcreteInfo VarVar = False
isConcreteInfo TauVar = False

isConcreteVar :: TcVar v => v -> Bool
isConcreteVar = isJust . isConcreteVar_maybe

isTouchableInfo :: MetaInfo -> Bool
isTouchableInfo _info = True

metaVarRef :: TcVar v => v -> IORef (MetaDetails (TcDetailsThing v))
metaVarRef v = case tcVarDetails v of
  MetaVar { mv_ref = ref } -> ref
  _ -> pprPanic "metaVarRef" (ppr v)

metaVarInfo :: TcVar v => v -> MetaInfo
metaVarInfo v = case tcVarDetails v of
  MetaVar { mv_info = info } -> info
  _ -> pprPanic "metaKiVarInfo" (ppr v)

setMetaVarTcLevel :: TcVar v => v -> TcLevel -> v
setMetaVarTcLevel v tclvl = case tcVarDetails v of
  details@(MetaVar {})
    -> setTcVarDetails v (details { mv_tclvl = tclvl })
  _ -> pprPanic "metaKiVarTcLevel" (ppr v)

isTcVarVar :: TcVar v => v -> Bool
isTcVarVar v = case tcVarDetails v of
  MetaVar { mv_info = VarVar } -> True
  _ -> False

isFlexi :: MetaDetails tk -> Bool
isFlexi Flexi = True
isFlexi _ = False

mkKiVarNamePairs :: [TcKiVar] -> [(Name, TcKiVar)]
mkKiVarNamePairs kvs = [(varName kv, kv) | kv <- kvs ]

ambigKvsOfKi :: AnyMonoKind -> [TcKiVar]
ambigKvsOfKi ki = filterAnyTcKiVar isAmbiguousVar kvs
  where
    kvs = varsOfMonoKindList ki

{- *********************************************************************
*                                                                      *
          Expanding and splitting kinds
*                                                                      *
********************************************************************* -}

-- tcSplitFunKi_maybe :: Kind -> Maybe (FunKiFlag, MonoKind, MonoKind)
-- tcSplitFunKi_maybe = splitFunKi_maybe

tcSplitMonoFunKi_maybe :: AnyMonoKind -> Maybe (FunKiFlag, AnyMonoKind, AnyMonoKind)
tcSplitMonoFunKi_maybe = splitMonoFunKi_maybe

tcSplitForAllKi_maybe :: AnyKind -> Maybe (AnyKiVar, AnyKind)
tcSplitForAllKi_maybe = splitForAllKi_maybe

-- tcSplitPiKi_maybe :: Kind -> Maybe (Either (KindVar, Kind) (FunKiFlag, MonoKind, MonoKind))
-- tcSplitPiKi_maybe ki = assert (isMaybeKiBinder ski) ski
--   where
--     ski = splitPiKi_maybe ki

--     isMaybeKiBinder (Just (Left (kv, _))) = isKiVar kv
--     isMaybeKiBinder _ = True

{- *********************************************************************
*                                                                      *
          Predicate kinds
*                                                                      *
********************************************************************* -}

isKiVarKcPred :: AnyPredKind -> Bool
isKiVarKcPred ki = case getPredKcKis_maybe ki of
  Just (_, kis) -> all isKiVarKi kis
  _ -> False

kiEvVarPred :: AnyKiCoVar AnyKiVar -> AnyMonoKind
kiEvVarPred var = varKind var

mkMinimalBy :: forall a. (a -> AnyPredKind) -> [a] -> [a]
mkMinimalBy get_pred xs = go preds_with_eqx []
  where
    preds_with_eqx :: [(AnyPredKind, [AnyPredKind], a)]
    preds_with_eqx = [ (pred, pred : eq_extras pred, x)
                     | x <- xs
                     , let pred = get_pred x ]

    eq_extras pred = case classifyPredKind pred of
                       EqPred k1 k2 -> [mkKiEqPred k2 k1]
                       _ -> []
 
    go :: [(AnyPredKind, [AnyPredKind], a)] -> [(AnyPredKind, [AnyPredKind], a)] -> [a]
    go [] min_preds = reverse (map thdOf3 min_preds)
    go (work_item@(p, _, _) : work_list) min_preds
      | EqPred k1 k2 <- classifyPredKind p
      , k1 `tcEqMonoKind` k2
      = go work_list min_preds
      | p `in_cloud` work_list || p `in_cloud` min_preds
      = go work_list min_preds
      | otherwise
      = go work_list (work_item : min_preds)

    in_cloud :: AnyPredKind -> [(AnyPredKind, [AnyPredKind], a)] -> Bool
    in_cloud p ps = or [ p `tcEqMonoKind` p' | (_, eqxs, _) <- ps, p' <- eqxs ]

{- *********************************************************************
*                                                                      *
          Expanding and splitting 
*                                                                      *
********************************************************************* -}

tcSplitForAllTyVarBinders :: AnyType -> ([AnyTyVarBinder], AnyType)
tcSplitForAllTyVarBinders ty = sty
  where sty = splitForAllForAllTyBinders ty

tcSplitTyLamTyVarBinders :: AnyType -> ([AnyTyVar AnyKiVar], AnyType)
tcSplitTyLamTyVarBinders ty = sty
  where sty = splitTyLamTyBinders ty

tcSplitBigLamTyVarBinders :: AnyType -> ([AnyKiVar], AnyType)
tcSplitBigLamTyVarBinders ty = sty
  where sty = splitBigLamTyBinders ty

{- *********************************************************************
*                                                                      *
      Classifying types
*                                                                      *
********************************************************************* -}

isRigidKi :: MonoKind kv -> Bool
isRigidKi ki = case ki of
  KiConApp {} -> True
  FunKi {} -> True
  _ -> False
