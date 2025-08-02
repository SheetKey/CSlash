{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CSlash.Tc.Utils.TcType
  ( module CSlash.Tc.Utils.TcType
  , TcTyVar, TcKiVar
  , AnyTypeCoercion, AnyTypeCoercionHole
  ) where

import Prelude hiding ((<>))

import CSlash.Core.Type
import CSlash.Core.Type.Rep
import CSlash.Core.Type.FVs
import CSlash.Core.Type.Subst
import CSlash.Core.Kind
import CSlash.Core.Kind.Compare
import CSlash.Core.Kind.FVs
import CSlash.Core.Kind.Subst
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
import CSlash.Data.List.SetOps (getNth)

import Data.IORef (IORef)

{- *********************************************************************
*                                                                      *
              Types
*                                                                      *
********************************************************************* -}

type AnyType = Type (AnyTyVar AnyKiVar) AnyKiVar
type TcType = Type (TcTyVar AnyKiVar) AnyKiVar

type AnyTvSubst = TvSubst (AnyTyVar AnyKiVar) AnyKiVar
type AnyKvSubst = KvSubst AnyKiVar

type AnyRhoType = AnyType
type AnyTauType = AnyType
type AnySigmaType = AnyType

type AnyTyVarBinder = VarBndr (AnyTyVar AnyKiVar) ForAllFlag
type TcTyVarBinder = VarBndr (TcTyVar AnyKiVar) ForAllFlag

type MonoAnyTyCon = AnyTyCon
type PolyAnyTyCon = AnyTyCon
type MonoTcTyCon = TcTyCon
type PolyTcTyCon = TcTyCon

type AnyPredType = AnyType

type AnyKind = Kind AnyKiVar
type AnyMonoKind = MonoKind AnyKiVar
type AnyPredKind = PredKind AnyKiVar

type TcKind = Kind TcKiVar
type TcMonoKind = MonoKind TcKiVar
type TcPredKind = PredKind TcKiVar

type TcKindCoercion = KindCoercion TcKiVar
type AnyKindCoercion = KindCoercion AnyKiVar

type TcKindCoercionHole = KindCoercionHole TcKiVar
type AnyKindCoercionHole = KindCoercionHole AnyKiVar

{- *********************************************************************
*                                                                      *
          ExpType: an "expected type" in the type checker
*                                                                      *
********************************************************************* -}

data ExpType
  = Check AnyType
  | Infer !InferResult

data InferResult

type ExpSigmaType = ExpType
type ExpRhoType = ExpType

instance Outputable ExpType where
  ppr (Check ty) = text "Check" <> braces (ppr ty)

mkCheckExpType :: AnyType -> ExpType
mkCheckExpType = Check

data ExpPatType
  = ExpFunPatTy ExpSigmaType
  | ExpForAllPatTy (ForAllBinder (AnyTyVar AnyKiVar))
  | ExpForAllPatKi AnyKiVar

mkCheckExpFunPatTy :: AnyType -> ExpPatType
mkCheckExpFunPatTy = ExpFunPatTy . mkCheckExpType

mkInvisExpPatType :: AnyTyVar AnyKiVar -> ExpPatType
mkInvisExpPatType tv = ExpForAllPatTy (Bndr tv Specified)

mkInvisExpPatKind :: AnyKiVar -> ExpPatType
mkInvisExpPatKind kv = ExpForAllPatKi kv

isVisibleExpPatType :: ExpPatType -> Bool
isVisibleExpPatType (ExpForAllPatTy (Bndr _ vis)) = isVisibleForAllFlag vis
isVisibleExpPatType (ExpFunPatTy {}) = True
isVisibleExpPatType (ExpForAllPatKi {}) = False

instance Outputable ExpPatType where
  ppr (ExpFunPatTy t) = ppr t
  ppr (ExpForAllPatTy tv) = text "forall" <+> ppr tv
  ppr (ExpForAllPatKi kv) = text "forall" <+> ppr kv

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

-- data ConcreteKvOrigin

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

-- not counting kinds since issues happened otherwise. Is this correct?
tcTypeLevel :: AnyType -> TcLevel
tcTypeLevel ty = tenv_lvl -- `maxTcLevel` kenv_lvl
  where
    (tenv, kenv) = varsOfTypeDSet ty
    tenv_lvl = nonDetStrictFoldDVarSet addt topTcLevel tenv
    kenv_lvl = nonDetStrictFoldDVarSet addk topTcLevel kenv

    add :: TcVar v => v -> TcLevel -> TcLevel
    add v lvl = lvl `maxTcLevel` varLevel v

    addt :: AnyTyVar AnyKiVar -> TcLevel -> TcLevel
    addt = handleAnyTv (\_ lvl -> lvl) add

    addk :: AnyKiVar -> TcLevel -> TcLevel
    addk = handleAnyKv (\_ lvl -> lvl) add

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
    go_mono bvs (KiPredApp pred k1 k2) = go_pred bvs pred k1 k2
    go_mono bvs (KiVarKi kv) = go_kv bvs kv
    go_mono bvs (BIKi {}) = False
    go_mono bvs (FunKi _ arg res) = go_mono bvs arg || go_mono bvs res

    go_kv bvs kv | kv `elemVarSet` bvs = False
                 | otherwise = handleAnyKv (const False) kv_pred kv

    go_pred :: MkVarSet AnyKiVar -> KiPredCon -> AnyMonoKind -> AnyMonoKind -> Bool
    go_pred bvs _ ki1 ki2 = go_mono bvs ki1 || go_mono bvs ki2

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

-- isConcreteVar_maybe :: TcVar v => v -> Maybe ConcreteKvOrigin
-- isConcreteVar_maybe kv 
--   | MetaVar { mv_info = info } <- tcVarDetails kv
--   = case info of
--       VarVar -> Nothing
--       TauVar -> Nothing
--   | otherwise
--   = Nothing

-- isConcreteKiVarKi_maybe :: AnyMonoKind -> Maybe (TcKiVar, ConcreteKvOrigin)
-- isConcreteKiVarKi_maybe (KiVarKi kv)
--   = handleAnyKv (const Nothing) (\kv -> (kv, ) <$> isConcreteVar_maybe kv) kv
-- isConcreteKiVarKi_maybe _ = Nothing

-- isConcreteInfo :: MetaInfo -> Bool
-- isConcreteInfo VarVar = False
-- isConcreteInfo TauVar = False

-- isConcreteVar :: TcVar v => v -> Bool
-- isConcreteVar = isJust . isConcreteVar_maybe

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

mkVarNamePairs :: IsVar kv => [kv] -> [(Name, kv)]
mkVarNamePairs kvs = [(varName kv, kv) | kv <- kvs ]

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

tcSplitPiKi_maybe
  :: AnyKind -> Maybe (Either (AnyKiVar, AnyKind) (FunKiFlag, AnyMonoKind, AnyMonoKind))
tcSplitPiKi_maybe ki = ski
  where
    ski = splitPiKi_maybe ki

isVisiblePiKiBndr :: Either (AnyKiVar, AnyKind) (FunKiFlag, AnyMonoKind, AnyMonoKind) -> Bool
isVisiblePiKiBndr (Left {}) = False
isVisiblePiKiBndr (Right (FKF_C_K, _, _)) = False
isVisiblePiKiBndr (Right (FKF_K_K, _, _)) = True

{- *********************************************************************
*                                                                      *
          Predicate kinds
*                                                                      *
********************************************************************* -}

isKiVarKcPred :: AnyPredKind -> Bool
isKiVarKcPred ki = case getPredKis_maybe ki of
  Just (_, k1, k2) -> all isKiVarKi [k1,k2]
  _ -> False

kiCoVarPred :: KiCoVar AnyKiVar -> AnyPredKind
kiCoVarPred = varKind

tyCoVarPred :: TyCoVar (AnyTyVar AnyKiVar) AnyKiVar -> AnyPredType
tyCoVarPred = varType

mkMinimalBy :: forall a. (a -> AnyPredKind) -> [a] -> [a]
mkMinimalBy get_pred xs = go preds_with_cox []
  where
    preds_with_cox :: [(AnyPredKind, [AnyPredKind], a)]
    preds_with_cox = [ (pred, pred : co_extras pred, x)
                     | x <- xs
                     , let pred = get_pred x ]

    co_extras pred = case classifyPredKind pred of
                       KiCoPred EQKi k1 k2 -> [ mkKiCoPred EQKi k2 k1
                                              , mkKiCoPred LTEQKi k1 k2
                                              , mkKiCoPred LTEQKi k2 k1 ]
                       KiCoPred LTKi k1 k2 -> [ mkKiCoPred LTEQKi k1 k2 ]
                       _ -> []
 
    go :: [(AnyPredKind, [AnyPredKind], a)] -> [(AnyPredKind, [AnyPredKind], a)] -> [a]
    go [] min_preds = reverse (map thdOf3 min_preds)
    go (work_item@(p, _, _) : work_list) min_preds
      | KiCoPred kc k1 k2 <- classifyPredKind p
      , k1 `tcEqMonoKind` k2, not (kc == LTKi)
      = go work_list min_preds
      | p `in_cloud` work_list || p `in_cloud` min_preds
      = go work_list min_preds
      | otherwise
      = go work_list (work_item : min_preds)

    in_cloud :: AnyPredKind -> [(AnyPredKind, [AnyPredKind], a)] -> Bool
    in_cloud p ps = or [ p `tcEqMonoKind` p' | (_, coxs, _) <- ps, p' <- coxs ]

{- *********************************************************************
*                                                                      *
          Expanding and splitting 
*                                                                      *
********************************************************************* -}

tcSplitForAllInvisTyVars :: AnyType -> ([AnyTyVar AnyKiVar], AnyType)
tcSplitForAllInvisTyVars = tcSplitSomeForAllTyVars isInvisibleForAllFlag

tcSplitSomeForAllTyVars :: (ForAllFlag -> Bool) -> AnyType -> ([AnyTyVar AnyKiVar], AnyType)
tcSplitSomeForAllTyVars argf_pred ty = split ty ty []
  where
    split _ (ForAllTy (Bndr tv argf) ty) tvs
      | argf_pred argf = split ty ty (tv:tvs)
    split orig_ty ty tvs | Just ty' <- coreView ty = split orig_ty ty' tvs
    split orig_ty _ tvs = (reverse tvs, orig_ty)

tcSplitForAllInvisBinders :: IsTyVar tv kv => Type tv kv -> ([tv], Type tv kv)
tcSplitForAllInvisBinders = splitForAllInvisTyBinders

tcSplitForAllTyVarBinders :: IsTyVar tv kv => Type tv kv -> ([ForAllBinder tv], Type tv kv)
tcSplitForAllTyVarBinders ty = sty
  where sty = splitForAllForAllTyBinders ty

tcSplitTyLamTyVarBinders :: IsTyVar tv kv => Type tv kv -> ([tv], Type tv kv)
tcSplitTyLamTyVarBinders ty = sty
  where sty = splitTyLamTyBinders ty

tcSplitBigLamTyVarBinders :: IsTyVar tv kv => Type tv kv -> ([kv], Type tv kv)
tcSplitBigLamTyVarBinders ty = sty
  where sty = splitBigLamTyBinders ty

tcSplitForAllTyVarsReqTVBindersN
  :: IsTyVar tv kv => Arity -> Type tv kv -> (Arity, [ForAllBinder tv], Type tv kv)
tcSplitForAllTyVarsReqTVBindersN n_req ty = split n_req ty ty []
  where
    split n_req _orig_ty (ForAllTy b@(Bndr _ argf) ty) bs
      | isVisibleForAllFlag argf, n_req > 0 = split (n_req - 1) ty ty (b:bs)
      | otherwise = split n_req ty ty (b:bs)
    split n_req orig_ty ty bs | Just ty' <- coreView ty = split n_req orig_ty ty' bs
    split n_req orig_ty _ bs = (n_req, reverse bs, orig_ty)

tcSplitSigma :: IsTyVar tv kv => Type tv kv -> ([kv], [tv], Type tv kv)
tcSplitSigma ty = case tcSplitBigLamTyVarBinders ty of
                    (kvs, ty') -> case tcSplitForAllInvisBinders ty' of
                                    (tvs, tau) -> (kvs, tvs, tau)

{- *********************************************************************
*                                                                      *
      Classifying types
*                                                                      *
********************************************************************* -}

isSigmaTy :: IsTyVar tv kv => Type tv kv -> Bool
isSigmaTy (ForAllTy (Bndr _ af) _) = isInvisibleForAllFlag af
isSigmaTy (TyLamTy {}) = panic "isSigmaTy TyLamTy"
isSigmaTy (BigTyLamTy {}) = True
isSigmaTy ty | Just ty' <- coreView ty = isSigmaTy ty'
isSigmaTy _ = False

isRhoTy :: IsTyVar tv kv => Type tv kv -> Bool
isRhoTy ty = not (isSigmaTy ty)

isRigidKi :: MonoKind kv -> Bool
isRigidKi ki = case ki of
  KiPredApp {} -> True
  BIKi {} -> True
  FunKi {} -> True
  _ -> False

{- *********************************************************************
*                                                                      *
        Visiblities
*                                                                      *
********************************************************************* -}

tyConVisibilities :: AnyTyCon -> [Bool]
tyConVisibilities tc = map (const False) fa_kvs ++ map (const False) invis_args ++ repeat True
  where
    (fa_kvs, monoki) = splitForAllKiVars (tyConKind tc)
    (invis_args, _) = splitInvisFunKis monoki

isNextTyConArgVisible :: AnyTyCon -> [AnyType] -> Bool
isNextTyConArgVisible tc tys
  = tyConVisibilities tc `getNth` length tys

isNextArgVisible :: AnyType -> Bool
isNextArgVisible ty
  | Just bndr <- tcSplitPiKi_maybe (typeKind ty) = isVisiblePiKiBndr bndr
  | otherwise = True
