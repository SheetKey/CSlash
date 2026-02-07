{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CSlash.Tc.Utils.TcType where

import Prelude hiding ((<>))

import CSlash.Cs.Pass

import CSlash.Core.Type
import CSlash.Core.Type.Compare
import CSlash.Core.Type.Rep
import CSlash.Core.Type.FVs
import CSlash.Core.Subst
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
import CSlash.Data.List.SetOps (getNth)

import Data.IORef (IORef)

{- *********************************************************************
*                                                                      *
              Types
*                                                                      *
********************************************************************* -}

type TauType = Type
type RhoType = Type
type SigmaType = Type

{- *********************************************************************
*                                                                      *
          ExpType: an "expected type" in the type checker
*                                                                      *
********************************************************************* -}

data ExpType
  = Check (Type Tc)
  | Infer !InferResult

data InferResult = IR
  { ir_uniq :: Unique
  , ir_lvl :: TcLevel
  , ir_ref :: IORef (Maybe (Type Tc)) }

type ExpSigmaType = ExpType
type ExpRhoType = ExpType

instance Outputable ExpType where
  ppr (Check ty) = text "Check" <> braces (ppr ty)
  ppr (Infer ir) = ppr ir

instance Outputable InferResult where
  ppr (IR { ir_uniq = u, ir_lvl = lvl })
    = text "Infer" <> braces (ppr u <> comma <> ppr lvl)

mkCheckExpType :: Type Tc -> ExpType
mkCheckExpType = Check

data ExpPatType
  = ExpFunPatTy ExpSigmaType
  | ExpForAllPatTy (ForAllBinder TcTyVar)
  | ExpForAllPatKiCo TcKiCoVar
  | ExpForAllPatKi TcKiVar

mkCheckExpFunPatTy :: Type Tc -> ExpPatType
mkCheckExpFunPatTy = ExpFunPatTy . mkCheckExpType

mkInvisExpPatType :: TcTyVar -> ExpPatType
mkInvisExpPatType tv = ExpForAllPatTy (Bndr tv Specified)

mkInvisExpPatKiCo :: TcKiCoVar -> ExpPatType
mkInvisExpPatKiCo kcv = ExpForAllPatKiCo kcv

mkInvisExpPatKind :: TcKiVar -> ExpPatType
mkInvisExpPatKind kv = ExpForAllPatKi kv

isVisibleExpPatType :: ExpPatType -> Bool
isVisibleExpPatType (ExpForAllPatTy (Bndr _ vis)) = isVisibleForAllFlag vis
isVisibleExpPatType (ExpFunPatTy {}) = True
isVisibleExpPatType (ExpForAllPatKi {}) = False
isVisibleExpPatType (ExpForAllPatKiCo {}) = False

instance Outputable ExpPatType where
  ppr (ExpFunPatTy t) = ppr t
  ppr (ExpForAllPatTy tv) = text "forall" <+> ppr tv
  ppr (ExpForAllPatKi kv) = text "forall" <+> ppr kv
  ppr (ExpForAllPatKiCo kcv) = text "forall" <+> ppr kcv

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

data TcLevel
  = TcLevel {-# UNPACK #-} !Int
  | QLInstVar

instance Outputable TcLevel where
  ppr (TcLevel us) = ppr us
  ppr QLInstVar = text "qlinst"

maxTcLevel :: TcLevel -> TcLevel -> TcLevel
maxTcLevel (TcLevel a) (TcLevel b)
  | a > b = TcLevel a
  | otherwise = TcLevel b
maxTcLevel _ _ = QLInstVar

minTcLevel :: TcLevel -> TcLevel -> TcLevel
minTcLevel (TcLevel a) (TcLevel b)
  | a < b = TcLevel a
  | otherwise = TcLevel b
minTcLevel tcla@(TcLevel {}) QLInstVar = tcla
minTcLevel QLInstVar tclb@(TcLevel {}) = tclb
minTcLevel QLInstVar QLInstVar = QLInstVar

topTcLevel :: TcLevel
topTcLevel = TcLevel 0

isTopTcLevel :: TcLevel -> Bool
isTopTcLevel (TcLevel 0) = True
isTopTcLevel _ = False

pushTcLevel :: TcLevel -> TcLevel
pushTcLevel (TcLevel us) = TcLevel (us + 1)
pushTcLevel QLInstVar = QLInstVar

strictlyDeeperThan :: TcLevel -> TcLevel -> Bool
strictlyDeeperThan (TcLevel lvl) (TcLevel ctxt_lvl) = lvl > ctxt_lvl
strictlyDeeperThan QLInstVar (TcLevel {}) = True
strictlyDeeperThan _ _ = False

deeperThanOrSame :: TcLevel -> TcLevel -> Bool
deeperThanOrSame (TcLevel v_tclvl) (TcLevel ctxt_tclvl) = v_tclvl >= ctxt_tclvl
deeperThanOrSame (TcLevel {}) QLInstVar = False
deeperThanOrSame _ _ = True

sameDepthAs :: TcLevel -> TcLevel -> Bool
sameDepthAs (TcLevel ctxt_tclvl) (TcLevel v_tclvl)
  = ctxt_tclvl == v_tclvl
sameDepthAs QLInstVar QLInstVar = True
sameDepthAs _ _ = False

checkTcLevelInvariant :: TcLevel -> TcLevel -> Bool
checkTcLevelInvariant lvla lvlb = lvla `deeperThanOrSame` lvlb

varLevel :: TcVar v => v -> TcLevel
varLevel v = case tcVarDetails v of
  MetaVar { mv_tclvl = tc_lvl } -> tc_lvl
  SkolemVar _ tc_lvl -> tc_lvl

-- TODO: not counting kinds since issues happened otherwise. Is this correct?
tcTypeLevel :: Type Tc -> TcLevel
tcTypeLevel ty = tenv_lvl -- `maxTcLevel` kenv_lvl
  where
    (tenv, _, kenv) = varsOfTypeDSet ty
    tenv_lvl = nonDetStrictFoldDVarSet add topTcLevel tenv
    -- kcenv_lvl = nonDetStrictFoldDVarSet add topTcLevel tenv -- not necessary! All kicovars are toplevel
    kenv_lvl = nonDetStrictFoldDVarSet add topTcLevel kenv

    add :: TcVar v => v -> TcLevel -> TcLevel
    add v lvl = lvl `maxTcLevel` varLevel v

tcMonoKindLevel :: MonoKind Tc -> TcLevel
tcMonoKindLevel ki = nonDetStrictFoldDVarSet add topTcLevel (varsOfMonoKindDSet ki)
  where
    add v lvl = lvl `maxTcLevel` varLevel v

tcKindLevel :: Kind Tc -> TcLevel
tcKindLevel ki = nonDetStrictFoldDVarSet add topTcLevel (varsOfKindDSet ki)
  where
    add v lvl = lvl `maxTcLevel` varLevel v

{-# INLINE any_rewritable_ki #-}
any_rewritable_ki :: (KiVar Tc -> Bool) -> MonoKind Tc -> Bool
any_rewritable_ki kv_pred = go_mono emptyVarSet
  where
    go_mono :: KiVarSet Tc -> MonoKind Tc -> Bool
    go_mono bvs (KiPredApp pred k1 k2) = go_pred bvs pred k1 k2
    go_mono bvs (KiVarKi kv) = go_kv bvs kv
    go_mono bvs (BIKi {}) = False
    go_mono bvs (FunKi _ arg res) = go_mono bvs arg || go_mono bvs res

    go_kv bvs kv | kv `elemVarSet` bvs = False
                 | otherwise = kv_pred kv

    go_pred :: KiVarSet Tc -> KiPredCon -> MonoKind Tc -> MonoKind Tc -> Bool
    go_pred bvs _ ki1 ki2 = go_mono bvs ki1 || go_mono bvs ki2

anyRewritableKiVar :: (KiVar Tc -> Bool) -> MonoKind Tc -> Bool
anyRewritableKiVar = any_rewritable_ki

any_rewritable_ty :: (TyVar Tc -> Bool) -> Type Tc -> Bool
{-# INLINE any_rewritable_ty #-}
any_rewritable_ty tv_pred = go emptyVarSet
  where
    go_tv bvs tv | tv `elemVarSet` bvs = False
                 | otherwise = tv_pred tv

    go :: TyVarSet Tc -> Type Tc -> Bool
    go bvs (TyConApp _ tys) = go_tc bvs tys
    go bvs (TyVarTy tv) = go_tv bvs tv
    go bvs (AppTy fun arg) = go bvs fun || go bvs arg
    go bvs (FunTy _ arg res) = go bvs arg || go bvs res
    go bvs (ForAllTy tv ty) = go (bvs `extendVarSet` binderVar tv) ty
    go bvs (ForAllKiCo _ ty) = go bvs ty
    go bvs (TyLamTy tv ty) = go (bvs `extendVarSet` tv) ty
    go bvs (BigTyLamTy _ ty) = go bvs ty
    go bvs (CastTy ty _) = go bvs ty
    go _ (KindCoercion _) = False
    go _ (Embed _) = False

    go_tc bvs tys = any (go bvs) tys

anyRewritableTyVar :: (TyVar Tc -> Bool) -> Type Tc -> Bool
anyRewritableTyVar = any_rewritable_ty

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

isQLInstVar :: TcVar v => v -> Bool
isQLInstVar v = case tcVarDetails v of
  MetaVar { mv_tclvl = QLInstVar } -> True
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

metaVarRef :: (Outputable v, TcVar v) => v -> IORef (MetaDetails (TcDetailsThing v))
metaVarRef v = case tcVarDetails v of
  MetaVar { mv_ref = ref } -> ref
  _ -> pprPanic "metaVarRef" (ppr v)

metaVarInfo :: (Outputable v, TcVar v) => v -> MetaInfo
metaVarInfo v = case tcVarDetails v of
  MetaVar { mv_info = info } -> info
  _ -> pprPanic "metaKiVarInfo" (ppr v)

setMetaVarTcLevel :: (Outputable v, TcVar v) => v -> TcLevel -> v
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

mkVarNamePairs :: IsVar v => [v] -> [(Name, v)]
mkVarNamePairs kvs = [(varName kv, kv) | kv <- kvs ]

ambigKvsOfKi :: MonoKind Tc -> [KiVar Tc]
ambigKvsOfKi ki = filter isAmbiguousVar kvs
  where
    kvs = varsOfMonoKindList ki

{- *********************************************************************
*                                                                      *
          Tau, sigma, rho
*                                                                      *
********************************************************************* -}

mkInfSigmaTy :: HasDebugCallStack => [TcKiVar] -> [TcTyVar] -> Type Tc -> Type Tc
mkInfSigmaTy kivars tyvars ty
  = mkSigmaTy (TcKiVar <$> kivars) (mkForAllBinders Inferred (TcTyVar <$> tyvars)) ty

mkSigmaTy
  :: HasDebugCallStack => [KiVar Tc] -> [ForAllBinder (TyVar Tc)] -> Type Tc -> Type Tc
mkSigmaTy kivars tybndrs tau = mkBigLamTys kivars $
                               mkForAllTys tybndrs $
                               tau

{- *********************************************************************
*                                                                      *
          Expanding and splitting kinds
*                                                                      *
********************************************************************* -}

-- tcSplitFunKi_maybe :: Kind -> Maybe (FunKiFlag, MonoKind, MonoKind)
-- tcSplitFunKi_maybe = splitFunKi_maybe

tcSplitMonoFunKi_maybe :: MonoKind p -> Maybe (FunKiFlag, MonoKind p, MonoKind p)
tcSplitMonoFunKi_maybe = splitMonoFunKi_maybe

tcSplitForAllKi_maybe :: Kind p -> Maybe (KiVar p, Kind p)
tcSplitForAllKi_maybe = splitForAllKi_maybe

tcSplitPiKi_maybe
  :: Kind Tc -> Maybe (Either (KiVar Tc, Kind Tc) (FunKiFlag, MonoKind Tc, MonoKind Tc))
tcSplitPiKi_maybe ki = ski
  where
    ski = splitPiKi_maybe ki

isVisiblePiKiBndr :: Either (KiVar Tc, Kind Tc) (FunKiFlag, MonoKind Tc, MonoKind Tc) -> Bool
isVisiblePiKiBndr (Left {}) = False
isVisiblePiKiBndr (Right (FKF_C_K, _, _)) = False
isVisiblePiKiBndr (Right (FKF_K_K, _, _)) = True

{- *********************************************************************
*                                                                      *
          Predicate types
*                                                                      *
********************************************************************* -}

tyCoVarPred :: TyCoVar Tc -> PredType Tc
tyCoVarPred = varType

mkMinimalBy_Ty :: forall a. (a -> PredType Tc) -> [a] -> [a]
mkMinimalBy_Ty get_pred xs = go preds_with_eqs []
  where
    preds_with_eqs :: [(PredType Tc, [PredType Tc], a)]
    preds_with_eqs = [ (pred, pred : eq_extras pred, x)
                     | x <- xs
                     , let pred = get_pred x ]

    eq_extras pred = case classifyPredType pred of
                       TyEqPred t1 t2 -> [mkTyEqPred t2 t1]
                       _ -> []

    go :: [(PredType Tc, [PredType Tc], a)] -> [(PredType Tc, [PredType Tc], a)] -> [a]
    go [] min_preds = reverse (map thdOf3 min_preds)
    go (work_item@(p, _, _) : work_list) min_preds
      | TyEqPred t1 t2 <- classifyPredType p
      , t1 `tcEqType` t2
      = go work_list min_preds

      | p `in_cloud` work_list || p `in_cloud` min_preds
      = go work_list min_preds

      | otherwise
      = go work_list (work_item : min_preds)

    in_cloud :: PredType Tc -> [(PredType Tc, [PredType Tc], a)] -> Bool
    in_cloud p ps = or [ p `tcEqType` p' | (_, eqs, _) <- ps, p' <- eqs ]

{- *********************************************************************
*                                                                      *
          Predicate kinds
*                                                                      *
********************************************************************* -}

isKiVarKcPred :: PredKind Tc -> Bool
isKiVarKcPred ki = case getPredKis_maybe ki of
  Just (_, k1, k2) -> all isKiVarKi [k1,k2]
  _ -> False

kiCoVarPred :: KiCoVar Tc -> PredKind Tc
kiCoVarPred = varKind

mkMinimalBy_Ki :: forall a. (a -> PredKind Tc) -> [a] -> [a]
mkMinimalBy_Ki get_pred xs = go preds_with_cox []
  where
    preds_with_cox :: [(PredKind Tc, [PredKind Tc], a)]
    preds_with_cox = [ (pred, pred : co_extras pred, x)
                     | x <- xs
                     , let pred = get_pred x ]

    co_extras pred = case classifyPredKind pred of
                       KiCoPred EQKi k1 k2 -> [ mkKiCoPred EQKi k2 k1
                                              , mkKiCoPred LTEQKi k1 k2
                                              , mkKiCoPred LTEQKi k2 k1 ]
                       KiCoPred LTKi k1 k2 -> [ mkKiCoPred LTEQKi k1 k2 ]
                       _ -> []
 
    go :: [(PredKind Tc, [PredKind Tc], a)] -> [(PredKind Tc, [PredKind Tc], a)] -> [a]
    go [] min_preds = reverse (map thdOf3 min_preds)
    go (work_item@(p, _, _) : work_list) min_preds
      | KiCoPred kc k1 k2 <- classifyPredKind p
      , k1 `tcEqMonoKind` k2, not (kc == LTKi)
      = go work_list min_preds
      | p `in_cloud` work_list || p `in_cloud` min_preds
      = go work_list min_preds
      | otherwise
      = go work_list (work_item : min_preds)

    in_cloud :: PredKind Tc -> [(PredKind Tc, [PredKind Tc], a)] -> Bool
    in_cloud p ps = or [ p `tcEqMonoKind` p' | (_, coxs, _) <- ps, p' <- coxs ]

{- *********************************************************************
*                                                                      *
          Expanding and splitting 
*                                                                      *
********************************************************************* -}

tcSplitBigLamKiVars :: Type Tc -> ([KiVar Tc], Type Tc)
tcSplitBigLamKiVars ty = split ty ty []
  where
    split _ (BigTyLamTy kv ty) kvs = split ty ty (kv:kvs)
    split orig_ty ty kvs | Just ty' <- coreView ty = split orig_ty ty' kvs
    split orig_ty _ kvs = (reverse kvs, orig_ty)

tcSplitForAllTyVarBinder_maybe :: Type Tc -> Maybe (ForAllBinder (TyVar Tc), Type Tc)
tcSplitForAllTyVarBinder_maybe ty | Just ty' <- coreView ty = tcSplitForAllTyVarBinder_maybe ty'
tcSplitForAllTyVarBinder_maybe (ForAllTy tv ty) = Just (tv, ty)
tcSplitForAllTyVarBinder_maybe _ = Nothing

tcSplitForAllInvisTyVars :: Type Tc -> ([TyVar Tc], Type Tc)
tcSplitForAllInvisTyVars = tcSplitSomeForAllTyVars isInvisibleForAllFlag

tcSplitSomeForAllTyVars :: (ForAllFlag -> Bool) -> Type Tc -> ([TyVar Tc], Type Tc)
tcSplitSomeForAllTyVars argf_pred ty = split ty ty []
  where
    split _ (ForAllTy (Bndr tv argf) ty) tvs
      | argf_pred argf = split ty ty (tv:tvs)
    split orig_ty ty tvs | Just ty' <- coreView ty = split orig_ty ty' tvs
    split orig_ty _ tvs = (reverse tvs, orig_ty)

tcSplitForAllInvisBinders :: HasPass p pass => Type p -> ([TyVar p], Type p)
tcSplitForAllInvisBinders = splitForAllInvisTyBinders

tcSplitForAllTyVarBinders :: HasPass p pass => Type p -> ([ForAllBinder (TyVar p)], Type p)
tcSplitForAllTyVarBinders ty = sty
  where sty = splitForAllForAllTyBinders ty

tcSplitForAllKiCoVars :: HasPass p pass => Type p -> ([KiCoVar p], Type p)
tcSplitForAllKiCoVars ty = sty
  where sty = splitForAllKiCoVars ty

tcSplitTyLamTyVarBinders :: HasPass p pass => Type p -> ([TyVar p], Type p)
tcSplitTyLamTyVarBinders ty = sty
  where sty = splitTyLamTyBinders ty

tcSplitBigLamTyVarBinders :: HasPass p pass => Type p -> ([KiVar p], Type p)
tcSplitBigLamTyVarBinders ty = sty
  where sty = splitBigLamTyBinders ty

tcSplitForAllTyVarsReqTVBindersN
  :: HasPass p pass
  => Arity -> Type p -> (Arity, [KiVar p], [KiCoVar p], [ForAllBinder (TyVar p)], Type p)
tcSplitForAllTyVarsReqTVBindersN n_req ty
  = case tcSplitBigLamTyVarBinders ty of
      (kvs, ty) ->
        case tcSplitForAllKiCoVars ty of
          (kcvs, ty) -> split n_req ty ty [] 
            where
              split n_req _orig_ty (ForAllTy b@(Bndr _ argf) ty) bs 
                | isVisibleForAllFlag argf, n_req > 0 = split (n_req - 1) ty ty (b:bs) 
                | isInvisibleForAllFlag argf = split n_req ty ty (b:bs) 
              split n_req orig_ty ty bs | Just ty' <- coreView ty = split n_req orig_ty ty' bs 
              split n_req orig_ty _ bs = (n_req, kvs, kcvs, reverse bs, orig_ty)

tcSplitSigma :: HasPass p pass => Type p -> ([KiVar p], [KiCoVar p], [TyVar p], Type p)
tcSplitSigma ty
  = case tcSplitBigLamTyVarBinders ty of
      (kvs, ty') -> case tcSplitForAllKiCoVars ty' of
                      (kcvs, ty'') -> case tcSplitForAllInvisBinders ty' of
                                        (tvs, tau) -> (kvs, kcvs, tvs, tau)

tcSplitNestedSigmaTys :: HasPass p pass => Type p -> ([KiVar p], [KiCoVar p], [TyVar p], Type p)
tcSplitNestedSigmaTys ty
  | (arg_tys, fun_kis, body_ty) <- tcSplitFunTys ty
  , (kvs1, kcvs1, tvs1, rho1) <- tcSplitSigma body_ty
  , not (null kvs1 && null kcvs1 && null tvs1)
  = let (kvs2, kcvs2, tvs2, rho2) = tcSplitNestedSigmaTys rho1
    in (kvs1 ++ kvs2, kcvs1 ++ kcvs2, tvs1 ++ tvs2, mkFunTys arg_tys fun_kis rho2)
  | otherwise = ([], [], [], ty)

tcSplitFunTys :: HasPass p pass => Type p -> ([Type p], [MonoKind p], Type p)
tcSplitFunTys ty = case tcSplitFunTy_maybe ty of
                     Nothing -> ([], [], ty)
                     Just (arg, ki, res) -> (arg:args, ki:kis, res')
                       where (args, kis, res') = tcSplitFunTys res

tcSplitFunTy_maybe :: HasPass p pass => Type p -> Maybe (Type p, MonoKind p, Type p)
tcSplitFunTy_maybe ty
  | Just ty' <- coreView ty = tcSplitFunTy_maybe ty'
tcSplitFunTy_maybe (FunTy ki arg res) = Just (arg, ki, res)
tcSplitFunTy_maybe _ = Nothing

tcSplitAppTy_maybe :: HasPass p pass => Type p -> Maybe (Type p, Type p)
tcSplitAppTy_maybe ty | Just ty' <- coreView ty = tcSplitAppTy_maybe ty'
tcSplitAppTy_maybe ty = tcSplitAppTyNoView_maybe ty

{- *********************************************************************
*                                                                      *
      Classifying types
*                                                                      *
********************************************************************* -}

isSigmaTy :: HasPass p pass => Type p -> Bool
isSigmaTy (ForAllTy (Bndr _ af) _) = isInvisibleForAllFlag af
isSigmaTy (ForAllKiCo _ _) = True
isSigmaTy (TyLamTy {}) = panic "isSigmaTy TyLamTy"
isSigmaTy (BigTyLamTy {}) = True
isSigmaTy ty | Just ty' <- coreView ty = isSigmaTy ty'
isSigmaTy _ = False

isRhoTy :: HasPass p pass => Type p -> Bool
isRhoTy ty = not (isSigmaTy ty)

isRigidTy :: Type p -> Bool
isRigidTy = panic "isRigidTy"

isRigidKi :: MonoKind p -> Bool
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

tyConVisibilities :: TyCon Tc -> [Bool]
tyConVisibilities tc = case tyConDetails tc of
  TcTyCon { tcTyConKind = kind } ->
    let (fa_kvs, monoki) = splitForAllKiVars kind
        (invis_args, _) = splitInvisFunKis monoki
    in map (const False) fa_kvs ++ map (const False) invis_args ++ repeat True
  other ->
    let kind = tyConKind other
        (fa_kvs, monoki) = splitForAllKiVars kind
        (invis_args, _) = splitInvisFunKis monoki
    in map (const False) fa_kvs ++ map (const False) invis_args ++ repeat True

isNextTyConArgVisible :: TyCon Tc -> [Type Tc] -> Bool
isNextTyConArgVisible tc tys
  = tyConVisibilities tc `getNth` length tys

isNextArgVisible :: Type Tc -> Bool
isNextArgVisible ty
  | Just bndr <- tcSplitPiKi_maybe (typeKind ty) = isVisiblePiKiBndr bndr
  | otherwise = True
